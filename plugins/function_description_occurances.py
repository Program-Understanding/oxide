
from core import api
from typing import Dict, Any, List
def function_description_occurances(args, opts):

    oids, invalid = api.valid_oids(args)

    descriptions = {}
    totalNumberOfFunctions = 0
    for oid in oids:
        subgraph_dict = api.retrieve("subgraph_descriptions", oid, opts=None)
        if subgraph_dict != None:
            for oid, function_descriptions in subgraph_dict.items():
                for address, description in function_descriptions.items():
                    if isinstance(description, list):
                        for eachDescription in description:
                            if eachDescription in descriptions:
                                descriptions[eachDescription] += 1
                                totalNumberOfFunctions += 1
                            else:
                                descriptions[eachDescription] = 1
                                totalNumberOfFunctions += 1
    
    
    for description in descriptions:
        descriptions[description] = [descriptions[description], round((descriptions[description]/totalNumberOfFunctions), 3)]

    sorted_descriptions = dict(sorted(descriptions.items(), key=lambda x: x[1][0], reverse=True))
    print("----------------------------------------")
    print("Total - Percentage \'Description\'\n")
    for description in sorted_descriptions:
        print(sorted_descriptions[description][0], " - ", sorted_descriptions[description][1], " \'", description.strip(), "\'")
    print("----------------------------------------")

        

exports = [function_description_occurances]