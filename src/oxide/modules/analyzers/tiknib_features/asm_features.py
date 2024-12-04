import networkx as nx
from functools import reduce

def get_asm_features(G, instructions):
    features = {}
    features["num_instructions"] = len(instructions)
    features["avg_num_instructions"] = len(instructions) / G.number_of_nodes()
    return features