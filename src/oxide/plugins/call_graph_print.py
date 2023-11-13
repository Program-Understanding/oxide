
#Will print a call_graph for the given object after it creates it within the call_graph analyzer

import networkx as nx
import matplotlib.pyplot as plt
import logging

from oxide.core import api

from typing import Dict, Any, List

#You must run the following commands to have the correct dependencies:
#pip install networkx
#pip install matplotlib
#sudo apt-get install graphviz
#pip install pydot

#I also had to run the following command on a linux machine:
#sudo apt-get install python3-tk

def call_graph_print(args, opts):
    oids, invalid = api.valid_oids(args)

    for oid in oids:
        call_graph = api.retrieve("call_graph", oid, opts=None)
        if call_graph is not None:
            for oid, call_graph in call_graph.items():
                pos = nx.nx_pydot.graphviz_layout(call_graph, prog="dot")
                nx.draw(call_graph, pos=pos, with_labels=True, node_size=1400, arrows=True)
                plt.show()

exports = [call_graph_print]
