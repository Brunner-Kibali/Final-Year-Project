# coding=utf-8
"""
AUTHOR: Brunner Ezra Kibali Toywa

PROJECT:

Adaptive Load Balancing and Traffic Engineering in Software-Defined Data Communication Networks

OBJECTIVES:

The aim of this project is to develop a load balancing and traffic engineering application that implements
dynamic and data driven management of network resources for high performance and low latency data transmission
in the network using OpenFlow-protocol-based SDN switches from a centralized controller.

DESIGN AND IMPLEMENTATION:

Making use of the OpenFlow-protocol-based RYU SDN controller. The Breadth First Search graph traversal
algorithm is used to find available paths. Path costs are calculated in the background using a thread.
The best path is chosen and updated every second based on the gathered traffic statistics.

Using OpenFlow Group tables (Select) and buckets to implement load balancing and traffic engineering across
multiple paths. Web server load balancing is implemented based on whether the MAC address of the client is ODD/EVEN.

Traffic flow modification and packet processing based on OpenFlow Version 1.3

All of the above is implemented programmatically using the Python version 3 programming language.
"""

from ryu.base import app_manager
from ryu.controller import mac_to_port
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.lib.packet.ether_types import ETH_TYPE_IP
from ryu.ofproto import ofproto_v1_3
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet
from ryu.lib.packet import arp
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.lib.packet import ipv6
from ryu.lib.packet import ether_types
from ryu.lib import mac, ip
from ryu.topology.api import get_switch, get_link
from ryu.app.wsgi import ControllerBase
from ryu.topology import event
from collections import defaultdict
from ryu.lib.mac import haddr_to_int
from operator import itemgetter
import os
import random
import time
import threading

# OSPF uses a shortest path first algorithm in order to build and calculate the shortest path to all known
# destinations. The shortest path is calculated with the use of the Dijkstra algorithm.
# REFERENCE_BW is the reference bandwidth constant used as in OSPF cost. Cisco Reference bandwidth = 1 Gbps
REFERENCE_BW = 10000000

DEFAULT_BW = 10000000

# MAX_PATHS is a constant set to limit number of paths used for routing.
MAX_PATHS = 2


class Load_Balancing_and_Traffic_Engineering(app_manager.RyuApp):
    """
    As an argument to the class, we pass ryu.base.app_manager.RyuApp (imported in the first line).
    From the Ryu API handbook, app_manager class is the central management of Ryu applications.
    It loads Ryu applications, provides contexts to them and routes messages among Ryu applications.
    """
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]  # Specifying the use of OpenFlow protocol version 1.3

    VIRTUAL_IP = '10.0.0.100'  # The virtual server IP
    SERVER1_IP = '10.0.0.1'  # host 1's IP
    SERVER1_MAC = '00:00:00:00:00:01'  # host 1's MAC
    SERVER1_PORT = 1  # host 1's port

    SERVER2_IP = '10.0.0.2'  # host 2's IP
    SERVER2_MAC = '00:00:00:00:00:02'  # host 2's MAC
    SERVER2_PORT = 2  # host 2's port

    def __init__(self, *args, **kwargs):
        super(Load_Balancing_and_Traffic_Engineering, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.topology_api_app = self
        self.datapath_list = {}
        self.arp_table = {}
        self.switches = []
        self.hosts = {}
        self.multipath_group_ids = {}
        self.group_ids = []
        # self.neighbor holds the adjacency matrix of the network/graph. It's of the form:
        # {SwithId: {Neighbour1:Port_Switch,Neighbour2:Port_Switch}}
        self.neighbor = defaultdict(dict)  # defaultdict means that if a key is not found in the dictionary,
        # then instead of a KeyError being thrown, a new entry is created. The type of this new entry is
        # given by the argument of defaultdict.
        # self.bandwidth contains a switch’s interfaces bandwidth.
        # Calling for two values only this time [switch][port]
        self.bandwidth = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        # self.logger.info("Initialized new Object instance data")

    def get_paths(self, src, dst):
        """
            Implementation of Breadth-First Search Algorithm (BFS). BFS searches the nodes of a graph by
            prioritizing those closer to its starting point. The algorithm adds all the neighbors of the nodes
            it visits in a queue and selects the nodes it visits according to the order in the queue.

            BFS keeps track of which vertices have already been visited using a queue, which is a data structure
            that allows us to insert and remove items, where the item removed is always the one that has been
            in the queue the longest (first in, first out)

            Step 1 : SET STATUS=1 (ready state) for each node in Graph.
            Step 2 : Enqueue the starting node A and set its STATUS = 2 (waiting state)
            Step 3 : Repeat Step 4 and 5 until QUEUE is empty
            Step 4 : Dequeue a node N. Process it and set its STATUS =3 (processed state)
            Step 5 : Enqueue all the neighbors of N that are in the ready state (whose STATUS = 1) and
            set their STATUS = 2 (waiting state)
            [END OF LOOP]
            Step 6 : EXIT

            In our topology, for h1 to reach h2, we can use the BFS algorithm to find two possible paths:
            1. s1 – s2 – s4
            2. s1 – s3 – s5 – s4
            """
        # src, dst is the routing target, which are switches (uses an integer OpenFlow dpid) connecting
        # the hosts.
        if src == dst:
            # host target is on the same switch
            # print("Source is the same as destination!")
            return [[src]]

        queue = [(src, [src])]
        paths = []
        while queue:
            (edge, path) = queue.pop()
            for vertex in set(self.neighbor[edge].keys()) - set(path):
                if vertex == dst:
                    paths.append(path + [vertex])
                else:
                    queue.append((vertex, path + [vertex]))
        print("Available paths from ", src, " to ", dst, " : ", paths)
        return paths  # Returns a list of paths.

    def get_link_cost(self, s1, s2):
        """
        The BFS algorithm returns an unweighted list of paths between source and destination, but we ought to
        analyze those paths so as to find the best path for forwarding traffic.

        To do this, we calculate the link cost between two switches using OSPF style:
        (https://www.cisco.com/c/en/us/support/docs/ip/open-shortest-path-first-ospf/7039-1.html#t6)

        OSPF Cost: The cost (also called metric) of an interface in OSPF is an indication of the overhead
        required to send packets across a certain interface.

        The cost of an interface is inversely proportional to the bandwidth of that interface. A higher
        bandwidth indicates a lower cost.

        There is more overhead (higher cost) and time delays involved in crossing a 56k serial line than
        crossing a 10M ethernet line.

        The formula used to calculate the cost is: cost= 100,000,000/bandwith in bps
        """
        port1 = self.neighbor[s1][s2]
        port2 = self.neighbor[s2][s1]
        link_bandwidth = min(self.bandwidth[s1][port1], self.bandwidth[s2][port2])
        link_cost = REFERENCE_BW / link_bandwidth
        return link_cost

    # To get the path cost, we sum up the link costs of the links in the path.
    def get_path_cost(self, path):
        """
        Get the path cost
        arg path is a list with all nodes in our route
        """
        path_cost = 0
        for i in range(len(path) - 1):
            path_cost += self.get_link_cost(path[i], path[i + 1])
        return path_cost

    # then we get the optimal according to the path cost.
    def get_optimal_paths(self, src, dst):
        """
        Get the n-most optimal paths according to MAX_PATHS
        """
        paths = self.get_paths(src, dst)
        paths_count = len(paths) if len(paths) < MAX_PATHS else MAX_PATHS
        return sorted(paths, key=lambda x: self.get_path_cost(x))[0:paths_count]

    def add_ports_to_paths(self, paths, first_port, last_port):
        """
        Add the ports to all switches and hosts for all paths
        """
        paths_and_ports = []
        ports = {}  # Dictionary with switchDPID structure: (Ingress_Port, Egress_Port)
        in_port = first_port
        for path in paths:
            for s1, s2 in zip(path[:-1], path[1:]):
                out_port = self.neighbor[s1][s2]
                ports[s1] = (in_port, out_port)
                in_port = self.neighbor[s2][s1]
            ports[path[-1]] = (in_port, last_port)
            paths_and_ports.append(ports)
        return paths_and_ports

    def generate_openflow_gid(self):
        """
        Returns a random OpenFlow group id
        """
        n = random.randint(0, 2 ** 32)
        while n in self.group_ids:
            n = random.randint(0, 2 ** 32)
        return n

    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst):
        """
        Installation of paths:

        In this part, we should define the property of packets for every switch to execute specific actions
        such as, forward or drop the packet.
        From the paths found in the previous step, we will install those paths to each switch.

        What it basically does is:

        List the paths available from source to destination.
        Loop through all the switches that contain a path.
        List all the ports in the switch that contains a path.
        If multiple ports in the switch contain a path, create a group table flow with type
        select (OFPGT_SELECT), or else just install a normal flow.

        To create a group table, we create buckets, which means group of actions, where we must specify:
        bucket weight: the weight of the bucket,
        watch port: the port to be watched (not needed for select group),
        watch group: other group tables to be watched (not needed),
        actions: your ordinary openflow action, i.e: output port.
        """
        computation_start = time.time()
        paths = self.get_optimal_paths(src, dst)
        pw = []  # pw is the path weight/cost (uses OSPF cost in previous step)

        for path in paths:
            """
            List the paths available from source to destination.
            """
            pw.append(self.get_path_cost(path))
            print(path, "cost = ", pw[len(pw) - 1])

        sum_of_pw = sum(pw) * 1.0
        paths_with_ports = self.add_ports_to_paths(paths, first_port, last_port)
        switches_in_paths = set().union(*paths)

        for node in switches_in_paths:

            dp = self.datapath_list[node]
            ofp = dp.ofproto
            ofp_parser = dp.ofproto_parser

            # defaultdict means that if a key is not found in the dictionary, then instead of a KeyError
            # being thrown, a new entry is created. The type of this new entry is given by the argument
            # of defaultdict.
            ports = defaultdict(list)

            actions = []
            i = 0

            for path in paths_with_ports:
                if node in path:
                    in_port = path[node][0]
                    out_port = path[node][1]
                    if (out_port, pw[i]) not in ports[in_port]:
                        ports[in_port].append((out_port, pw[i]))
                i += 1

            for in_port in ports:
                """ 
                Here we emulate a router, where we identify a packet by their destination IP (ipv4_dst). 
                Interesting to note that there is an extra field eth_type, which specifies the EtherType. 
                
                As you can see, marked clearly by the variable names, we will identify IP and ARP packets that 
                arrive at the switch.

                Why ARP? For L3 (IP Address) routing, we need to be able resolve the corresponding MAC address 
                for an IP, which is important for host discovery in a topology. 
                
                It literally is the first packet sent from a host if it wants to reach or communicate with 
                another host in the network, by sending a broadcast packet, so it is essential we handle it 
                correctly. Otherwise, bad things could happen, i.e: ARP packets flooding in a loop, which could
                cause a network to be unusable.
                
                Here we define two packets, ip and arp by using different ether type, 0x0800 for ipv4 and 
                0x0806 for arp (address resolution protocol). 
                Reference: https://en.wikipedia.org/wiki/EtherType#Examples
                """
                match_ip = ofp_parser.OFPMatch(
                    eth_type=0x0800,
                    ipv4_src=ip_src,
                    ipv4_dst=ip_dst
                )
                match_arp = ofp_parser.OFPMatch(
                    eth_type=0x0806,
                    arp_spa=ip_src,
                    arp_tpa=ip_dst
                )

                out_ports = ports[in_port]
                # print(out_ports)

                if len(out_ports) > 1:
                    """ 
                    After getting all available paths, we need to add them into the switch, and by 
                    using the SELECT group table, we achieve the round robin technique. We just changed bucket 
                    weight for each path to do a simple round robin based on different path cost.

                    SELECT group table: 
                    (reference: https://www.opennetworking.org/images/stories/downloads/sdn-resources/onf-specifications/openflow/openflow-switch-v1.5.0.noipr.pdf)
                    select: Execute one bucket in the group. Packets are processed by a single bucket in the group, 
                    based on a switch-computed selection algorithm (e.g. hash on some user-configured tuple or simple 
                    round robin). All configuration and state for the selection algorithm is external to OpenFlow. 
                    
                    The selection algorithm should implement equal load sharing and can optionally be based on 
                    bucket weights. When a port specified in a bucket in a select group goes down, the switch may restrict 
                    bucket selection to the remaining set (those with forwarding actions to live ports) instead of dropping 
                    packets destined to that port. 
                    
                    This behavior may reduce the disruption of a downed link or switch.   
                    > bucket weight: the weight of the bucket     
                    > actions: your ordinary openflow action, (output port)
                    """
                    group_id = None
                    group_new = False

                    if (node, src, dst) not in self.multipath_group_ids:
                        group_new = True
                        self.multipath_group_ids[
                            node, src, dst] = self.generate_openflow_gid()
                    group_id = self.multipath_group_ids[node, src, dst]

                    # we specify buckets, here which we insert multiple output actions for each port
                    # that contains a path to the group table.
                    buckets = []
                    # print("node at ", node, " out ports : ", out_ports)
                    for port, weight in out_ports:
                        """
                        For the bucket weight, we used a simple weight formula which utilizes the path cost/weight 
                        in the previous step. Basically, it finds the ratio of the path weight to the total path 
                        weight of the available paths.
                        
                        When it comes to path weight or cost where ideally we want to use the shortest path first, 
                        then lower is better. While in the context of buckets in OpenFlow Group tables, the 
                        priority of choosing a bucket is with the highest bucket weight, hence higher is better.

                        By using that formula, we can expect that the lower the path weight, then the higher 
                        the bucket weight.
                        
                        Looking back at our topology, we can calculate the path weight for the two 
                        paths available, assuming every link/edge is assigned a weight of 1:

                        pw1 = (s1-s3) + (s3-s5) = 2
                        pw2  = (s1-s2) + (s2-s4) + (s4-s5) = 3
                        
                        bw1 = (1 – 2/5) * 10 = 6
                        bw2 = (1 – 3/5) * 10 = 4
                        """
                        bucket_weight = int(round((1 - weight / sum_of_pw) * 10))
                        bucket_action = [ofp_parser.OFPActionOutput(port)]
                        buckets.append(
                            ofp_parser.OFPBucket(
                                weight=bucket_weight,
                                watch_port=port,
                                watch_group=ofp.OFPG_ANY,
                                actions=bucket_action
                            )
                        )

                    if group_new:
                        req = ofp_parser.OFPGroupMod(
                            dp, ofp.OFPGC_ADD, ofp.OFPGT_SELECT, group_id,
                            buckets
                        )
                        dp.send_msg(req)
                    else:
                        req = ofp_parser.OFPGroupMod(
                            dp, ofp.OFPGC_MODIFY, ofp.OFPGT_SELECT,
                            group_id, buckets)
                        dp.send_msg(req)

                    actions = [ofp_parser.OFPActionGroup(group_id)]

                    self.add_flow(dp, 32768, match_ip, actions)
                    self.add_flow(dp, 1, match_arp, actions)

                elif len(out_ports) == 1:
                    actions = [ofp_parser.OFPActionOutput(out_ports[0][0])]

                    self.add_flow(dp, 32768, match_ip, actions)
                    self.add_flow(dp, 1, match_arp, actions)
        print("Path installation finished in ", time.time() - computation_start)
        return paths_with_ports[0][src][1]

    def add_flow(self, datapath, priority, match, actions, buffer_id=None):
        """
        Method Provided by the source Ryu library.
        A flow is defined as a set of actions to be applied on a criteria of a network packet.
        For example, it answers what should be done to a packet which has a source IP address 10.0.0.1 and
        destination IP address 10.0.0.2 (the criteria).
        We can either forward the packet or drop the packet (the action), or do other crazy things.
        """
        # print("Adding flow", match, actions)
        # self.logger.info("Now adding flow")
        ofproto = datapath.ofproto  # Library definition for use of OpenFlow versions
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
        # Add flow in the flow table of the virtual switch
        datapath.send_msg(mod)
        # self.logger.info("Done adding flows")

    def run_check(self, ofp_parser, dp):
        """
        Every second the thread polls the switches about the port status and the PortStatsReq is sent
        """
        threading.Timer(1.0, self.run_check, args=(ofp_parser, dp)).start()

        req = ofp_parser.OFPPortStatsRequest(dp)
        # self.logger.info(f"Port Stats Request has been sent for sw: {dp} !")
        dp.send_msg(req)

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def _switch_features_handler(self, ev):
        """
        To send packets for which we dont have right information to the controller
        Method Provided by the source Ryu library.
        """
        # print("switch_features_handler is called")
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        # install table miss flow entry
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions)
        # self.logger.info("Set Config data for new Object Instance")

    @set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    def port_desc_stats_reply_handler(self, ev):
        """
        Reply to the OFPPortStatsRequest, visible beneath
        """
        # switch = ev.msg.datapath
        switch_dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            self.bandwidth[switch_dpid][p.port_no] = p.curr_speed  # Stores port capacity in Mbit/s

            # self.logger.info(f"Switch: {switch_dpid} Port: {p.port_no} Bw: {self.bandwidth[switch_dpid][p.port_no]}")

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        """This is called when Ryu receives an OpenFlow packet_in message.
        When Ryu receives a packet_in message, a ofp_event.EventOFPPacketIn event is raised.

        The set_ev_cls decorator tells Ryu when the associated function, packet_in_handler should be called.
        The first argument of the set_ev_cls decorator indicates an event that makes function call.

        As you expect easily, every time a ofp_event.EventOFPPacketIn event is raised, this function is called.
        The second argument indicates the state of the switch when you want to allow Ryu to handle an event.

        Probably, you want to ignore OpenFlow packet_in messages before the handshake between Ryu and the switch
        finishes. Using MAIN_DISPATCHER as the second argument means this function is called only after the
        negotiation completes. MAIN_DISPATCHER denotes the normal state of the switch. During the initialization
        stage, the switch is in HANDSHAKE_DISPATCHER state!

        The Ryu API exposes event handlers using decorators, where we can listen for OpenFlow events,
        such as when a switch enters the network, or when a new link is connected, etc.
        Here we listen to the `ofp_event.EventOFPPacketIn` event, which handles whenever a packet arrives
        at the controller. We can try sniffing the packets by extracting it from the event object.
        """
        # self.logger.info("Entered main mode event handling")
        # If you hit this you might want to increase
        # the "miss_send_length" of your switch
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes", ev.msg.msg_len, ev.msg.total_len)

        # fetch all details of the event
        msg = ev.msg  # ev.msg is a data structure that contains the received packet.
        datapath = msg.datapath  # msg.datapath is an object inside that data structure that represents a datapath (switch).
        ofproto = datapath.ofproto  # object that represents the OpenFlow protocol that Ryu and the switch negotiated.
        parser = datapath.ofproto_parser  # object that represents the OpenFlow protocol that Ryu and the switch negotiated.
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        # eth = pkt.get_protocols(ethernet.ethernet)
        etherFrame = pkt.get_protocol(ethernet.ethernet)
        # For most TCP/IP network traffic, you will see that the first packet sent from a host is an ARP
        # packet, like explained previously. That is what we will be processing in this method.
        # We can extract the ARP packet headers like this:
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        # avoid broadcast from LLDP
        if etherFrame.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
            return

        if pkt.get_protocol(ipv6.ipv6):  # Drop the IPV6 Packets.
            match = parser.OFPMatch(eth_type=etherFrame.ethertype)
            actions = []
            self.add_flow(datapath, 1, match, actions)
            return None

        dst = etherFrame.dst
        src = etherFrame.src
        dpid = datapath.id
        self.mac_to_port.setdefault(dpid, {})

        # self.logger.info("packet in %s %s %s %s", dpid, src, dst, in_port)

        # Next, we process the packet as below. First we maintain a host map in the topology as self.hosts ,
        # that maps the host MAC address to its connecting switch (identified by dpid or datapath ID in OpenFlow)
        # and the port number it is connected on the switch.

        # We initialize out_port, guessing by the name, it is where we specify the output port, which port the
        # switch will forward the packet to. As a fallback, we set it as ofproto.OFPP_FLOOD which means we
        # flood all ports of the switch.

        # Now the arp_pkt. We can extract the source and destination IP address of the packet, and the ARP
        # opcode.  From the opcode, we can differentiate if the packet is an ARP reply packet or an ARP request.
        # First we check if it is ARP reply, which means a host replied the ARP broadcast.

        # We also maintain an ARP table to map IP addresses to its corresponding MAC addresses as self.arp_table.
        # So whenever ARP reply is received, we save its source to the ARP table.

        # From that, we can be sure the destination host exists and a path(s) are available, thus we can install
        # a path to the switches.
        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)

        # learn a mac address to avoid FLOOD next time.
        self.mac_to_port[dpid][src] = in_port

        if dst in self.mac_to_port[dpid]:
            out_port = self.mac_to_port[dpid][dst]
        else:
            out_port = ofproto.OFPP_FLOOD

        # Handle ARP packet
        if arp_pkt:
            # print(dpid, pkt)
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip

            # The load balancer doesn’t just distribute the incoming requests but it also acts as a wall in
            # between the server pool and clients. The client should not know the identity of the server that
            # is servicing its request or that any server is down or the number of servers present.

            # Thus, it’s the load balancer’s job to act as the middle man that hides the servers behind it and
            # spoofs the identity of the servers.

            # A virtual IP and MAC are specified as the address of the load balancer and is not used in the
            # network for any other device. In the network, the clients will connect to this IP and MAC,
            # believing it’s the website’s server address that is answering the requests. The servers are
            # assigned IP addresses that are not exposed to the clients and there might be more than one
            # load balancer behind a virtual IP.

            # For a first-time ARP connection:
            # 1. The client creates an ARP packet and uses the virtual MAC as the destination address
            # and the source address as its own MAC.
            # 2. The switch present at the load balancer site will receive it and because the packet
            # doesn’t match any flow entry it is forwarded to the SDN controller. The controller will
            # parse the packet and extract the source MAC and the in port.
            if dst_ip == self.VIRTUAL_IP and arp_pkt.opcode == arp.ARP_REQUEST:
                self.logger.info("***************************")
                self.logger.info("---Handle ARP Packet---")
                # Build an ARP reply packet using source IP and source MAC
                reply_packet = self.generate_arp_reply(arp_pkt.src_ip, arp_pkt.src_mac)
                actions = [parser.OFPActionOutput(in_port)]
                packet_out = parser.OFPPacketOut(datapath=datapath, in_port=ofproto.OFPP_ANY,
                                                 data=reply_packet.data, actions=actions, buffer_id=0xffffffff)
                datapath.send_msg(packet_out)
                self.logger.info("Sent the ARP reply packet")
                return

            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip)  # reverse
            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip)
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip)  # reverse

        # Handle TCP Packet
        if etherFrame.ethertype == ETH_TYPE_IP:
            self.logger.info("***************************")
            self.logger.info("---Handle TCP Packet---")

            packet_handled = self.handle_tcp_packet(datapath, in_port, ip_pkt, parser, dst, src)
            self.logger.info("TCP packet handled: " + str(packet_handled))
            if packet_handled:
                return

        # print(pkt)
        # OFPActionOutput class is used with a packet_out message to specify a switch port
        # that you want to send the packet out of.
        actions = [parser.OFPActionOutput(out_port)]

        # install a flow to avoid packet_in next time
        if out_port != ofproto.OFPP_FLOOD:
            match = parser.OFPMatch(in_port=in_port, eth_dst=dst, eth_src=src)
            # verify if we have a valid buffer_id, if yes avoid to send both
            # flow_mod & packet_out
            if msg.buffer_id != ofproto.OFP_NO_BUFFER:
                self.add_flow(datapath, 10, match, actions, msg.buffer_id)
                return
            else:
                self.add_flow(datapath, 10, match, actions)

        # Send if other packet
        data = None
        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data

        # OFPPacketOut class is used to build a packet_out message.
        out = parser.OFPPacketOut(
            datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port,
            actions=actions, data=data)
        # By using datapath class's send_msg method, you can send an OpenFlow message object
        # to the ports defined in the actions variable.
        datapath.send_msg(out)

    # Source IP and MAC passed here now become the destination for the reply packet
    def generate_arp_reply(self, dst_ip, dst_mac):
        """
        An ARP reply is generated in the controller code with the source address as load
        balancers and destination as client address and passed to the switch which transmits it
        back to the client.

        For the future, a flow is created (load balancer to client) and inserted
        in the switch that modifies the packet header and changes the destination MAC to that
        of the client and source MAC to load balancers. So, further ARP requests from the same client on that
        in port will automatically be replied to by the switch at line rate speed.

        To the client which started the connection it would look like the server (load balancer) has replied
        with its MAC.

        For successive ARP connections:

        After the first encounter, the controller inserts the flow table entries into the switch so the switch
        would match the packet with a flow and according to priority take the corresponding action at line rate
        speed just like a legacy switch.
        """
        self.logger.info("Generating ARP Reply Packet")
        self.logger.info("ARP request client ip: " + dst_ip + ", client mac: " + dst_mac)
        arp_target_ip = dst_ip  # the sender ip
        arp_target_mac = dst_mac  # the sender mac
        # Making the load balancer IP as source IP
        src_ip = self.VIRTUAL_IP

        if haddr_to_int(arp_target_mac) % 2 == 1:
            src_mac = self.SERVER1_MAC
        else:
            src_mac = self.SERVER2_MAC
        self.logger.info("Selected server MAC: " + src_mac)

        pkt = packet.Packet()
        pkt.add_protocol(
            ethernet.ethernet(
                dst=dst_mac, src=src_mac, ethertype=ether_types.ETH_TYPE_ARP)
        )
        pkt.add_protocol(
            arp.arp(opcode=arp.ARP_REPLY, src_mac=src_mac, src_ip=src_ip,
                    dst_mac=arp_target_mac, dst_ip=arp_target_ip)
        )
        pkt.serialize()
        self.logger.info("Done with processing the ARP reply packet")
        return pkt

    def handle_tcp_packet(self, datapath, in_port, ip_header, parser, dst_mac, src_mac):
        """
        For a first-time TCP/UDP connection:

        1. The client creates a TCP request and uses the virtual IP and MAC as the destination
        address and the source address as its own IP and MAC.

        2. The switch present at the load balancer site will receive it and because the packet
        doesn’t match any flow entry it is forwarded to the SDN controller. The controller will
        parse the packet and extract the source IP and MAC and the in_port. According to the
        algorithm used for load balancing (in our case odd/even MAC), one server will be chosen to
        handle the connection.

        3. For that flow a forward action (client to server) will be inserted in the switch that
        modifies the packet header and changes the destination IP and MAC to that of the
        selected server. Then it is simply given to the switch to transmit it to that server. Also for
        the flow in reverse, another (reverse) action (server to client) will be inserted that
        changes the source IP and MAC to that of the load balancer (virtual IP and MAC).

        4. The selected server will receive the packet and take some action then generate a
        reply/response packet with the destination IP and MAC as the source IP and MAC of
        the packet that was received. This makes sure that the packet goes to the client from
        where the request originated.

        5. The reply packet would flow through the switch and the in_port would match that of the
        server while the out_port would match that of the client machine so a reverse action
        would be created by the switch. The packet header will be edited and the source IP and
        MAC will be changed to that of the load balancer and put back in the network.

        6. To the client which started the connection it would look like the same server (load
        balancer) has replied, though the actual server addresses has been spoofed.

        For successive TCP/UDP connections:

        After the first encounter, the SDN controller would have inserted the entries into the switch flow
        table. From now on the switch would match the packet with a flow and priority and take the
        corresponding action at line rate speed (the actual speed with which the bits are sent onto the wire)
        just like a legacy switch.
        """
        packet_handled = False

        if ip_header.dst == self.VIRTUAL_IP:
            if dst_mac == self.SERVER1_MAC:
                server_dst_ip = self.SERVER1_IP
                server_out_port = self.SERVER1_PORT
            else:
                server_dst_ip = self.SERVER2_IP
                server_out_port = self.SERVER2_PORT

            # Route to server
            match = parser.OFPMatch(in_port=in_port, eth_type=ETH_TYPE_IP, ip_proto=ip_header.proto,
                                    ipv4_dst=self.VIRTUAL_IP)

            actions = [parser.OFPActionSetField(ipv4_dst=server_dst_ip),
                       parser.OFPActionOutput(server_out_port)]

            self.add_flow(datapath, 20, match, actions)
            self.logger.info("<==== Added TCP Flow- Route to Server: " + str(server_dst_ip) +
                             " from Client :" + str(ip_header.src) + " on Switch Port:" +
                             str(server_out_port) + "====>")

            # Reverse route from server
            match = parser.OFPMatch(in_port=server_out_port, eth_type=ETH_TYPE_IP,
                                    ip_proto=ip_header.proto,
                                    ipv4_src=server_dst_ip,
                                    eth_dst=src_mac)
            actions = [parser.OFPActionSetField(ipv4_src=self.VIRTUAL_IP),
                       parser.OFPActionOutput(in_port)]

            self.add_flow(datapath, 20, match, actions)
            self.logger.info("<==== Added TCP Flow- Reverse route from Server: " + str(server_dst_ip) +
                             " to Client: " + str(src_mac) + " on Switch Port:" +
                             str(in_port) + "====>")
            packet_handled = True
        return packet_handled

    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch_dp = ev.switch.dp
        switch_dpid = switch_dp.id
        ofp_parser = switch_dp.ofproto_parser

        # self.logger.info(f"Switch has been plugged in PID: {switch_dpid}")

        if switch_dpid not in self.switches:
            self.switches.append(switch_dpid)
            self.datapath_list[switch_dpid] = switch_dp

            # Request port/link descriptions, useful for obtaining bandwidth
            self.run_check(ofp_parser, switch_dp)  # Thread function running in the background every 1s

    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        # print(ev)
        switch = ev.switch.dp.id
        if switch in self.switches:
            try:
                self.switches.remove(switch)
                del self.datapath_list[switch]
                del self.neighbor[switch]
            except KeyError:
                self.logger.info(f"Switch has been already plugged off PID{switch}!")

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        self.neighbor[s1.dpid][s2.dpid] = s1.port_no
        self.neighbor[s2.dpid][s1.dpid] = s2.port_no
        # self.logger.info(f"Link between switches has been established, SW1 DPID:"
        # f" {s1.dpid}:{s2.port_no} SW2 DPID: {s2.dpid}:{s2.port_no}")

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        s1 = ev.link.src
        s2 = ev.link.dst
        # Exception handling if switch already deleted
        try:
            del self.neighbor[s1.dpid][s2.dpid]
            del self.neighbor[s2.dpid][s1.dpid]
        except KeyError:
            self.logger.info("Link has been already plugged off!")
            pass


""" 
Events: You repeatedly saw the term event in the above code. In event driven programming, the flow of the program 
is controlled by events, which are raised by messages received by the system (e.g. EventOFPPacketIn is raised when 
the packet_in message is received by Ryu from the OpenFlow enabled switch. 

OpenFlow is a protocol using which the controller (Ryu, PC) and the infrastructure (or switch) communicate. 
Messages like packet_in are exactly what the communication between the two looks like using the  OpenFlow protocol!

Observe events: A Ryu application can register itself to listen for specific events using 
ryu.controller.handler.set_ev_cls decorator. A decorator is a design pattern in Python that allows a user to add 
new functionality to an existing object without modifying its structure. Decorators are usually called before the 
definition of a function you want to decorate. 

For example, the set_ev_cls decorator:
@set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER) tells Ryu when the associated function; packet_in_handler 
should be called. The first argument of the set_ev_cls decorator indicates an event that makes function call. 

The actual decorator function set_event_cls() is defined in handler.py: 
https://github.com/faucetsdn/ryu/blob/master/ryu/controller/handler.py
"""
