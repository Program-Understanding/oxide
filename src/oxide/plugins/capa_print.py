""" Plugin: Prints out capa results for an oid.
"""
import os
import json
from oxide.core import api
import tabulate

# Work in progress - Dylan
def capa_print(args, opts):
    """
        Prints capa results for an oid
        Syntax: capa_print <oid>
    """
    oid, invalid = api.valid_oids(args)
    output = api.retrieve("capa_match", oid, oid)

    for rule in output:
        print("OS: " + output[rule]['os'] + '\n' + "Architecure: " + output[rule]['arch'] + '\n'+ "Format: " + output[rule]['format'] + '\n')
        print(
        "Attack Tactic: " + output[rule]['attack_tactic'] + '\n' +
        "Attack Technique: " + output[rule]['attack_technique'] + '\n'
        )
        print(
        "Capability: " + str(rule) + '\n' +
        "Namespace: " + output[rule]['namespace'] + '\n' +
        "Found At Function: " + str(output[rule]['function_found']) + ' - ' +  str(output[rule]['address_found']) + '\n'
        )


exports = [capa_print]

