#!/usr/bin/python

"""
              Switch2 ----switch4
            /                       \
h1 ---Switch1                        Switch5-----h2
            \                       /
            --------Switch3 ------

Reference:
Introduction to Mininet: https://github.com/mininet/mininet/wiki/Introduction-to-Mininet#apilevels

Starting RYU Controller:
ryu-manager --observe-links my_load_balancer.py
"""

from mininet.cli import CLI
from mininet.log import setLogLevel
from mininet.net import Mininet
from mininet.topo import Topo
from mininet.node import RemoteController, OVSSwitch


class Project_Topo(Topo):
    """Project topology with five switches and two hosts"""

    def build(self):
        # Create two hosts.
        h1 = self.addHost('h1')
        h2 = self.addHost('h2')
        # h1 = self.addHost('h1', mac="00:00:00:00:00:01", ip="192.168.1.1/24")
        # h2 = self.addHost('h2', mac="00:00:00:00:00:02", ip="192.168.1.2/24")

        # Create five switches
        s1 = self.addSwitch('s1', protocols='OpenFlow13')
        s2 = self.addSwitch('s2', protocols='OpenFlow13')
        s3 = self.addSwitch('s3', protocols='OpenFlow13')
        s4 = self.addSwitch('s4', protocols='OpenFlow13')
        s5 = self.addSwitch('s5', protocols='OpenFlow13')
        # s1 = self.addSwitch('s1')

        # Add links between the switches and hosts
        self.addLink(h1, s1)
        self.addLink(h2, s5)

        # Add links between the switches
        self.addLink(s1, s2)
        self.addLink(s1, s3)
        self.addLink(s2, s4)
        self.addLink(s4, s5)
        self.addLink(s3, s5)


def runProject_Topo():
    """Bootstrap a Mininet network using the Project_Topo Topology"""

    # Create an instance of our topology
    topo = Project_Topo()

    # Create a network based on the topology using OVS and controlled by
    # a remote controller.
    net = Mininet(
        topo=topo,
        controller=lambda name: RemoteController(name, ip='127.0.0.1'),
        switch=OVSSwitch,
        autoSetMacs=True)

    # Actually start the network
    net.start()
    print("Topology is up, lets ping")
    net.pingAll()

    # Drop the user in to a CLI so user can run commands.
    CLI(net)

    # After the user exits the CLI, shutdown the network.
    net.stop()


if __name__ == '__main__':
    # This runs if this file is executed directly
    setLogLevel('info')
    runProject_Topo()

# Allows the file to be imported using `mn --custom <filename> --topo project-topo`
topos = {
    'minimal': Project_Topo
}
