
from oxide.core import api
from typing import Dict, Any, List
def function_description_occurances(args, opts):

    oids, invalid = api.valid_oids(args)

    descriptions = {}
    subgraphAppearances = {}
    totalNumberOfFunctions = 0
    for oid in oids:
        subgraph_dict = api.retrieve("subgraph_descriptions", oid, opts=None)
        if subgraph_dict != None:
            for oid, function_descriptions in subgraph_dict.items():
                descriptionsFound = function_descriptions['All Descriptions']
                for address, description in descriptionsFound.items():
                    for eachDescription in description:
                        if isinstance(eachDescription, dict):
                            DictDescription = list(eachDescription)[0]
                            if DictDescription in descriptions:
                                descriptions[DictDescription] += 1
                                totalNumberOfFunctions += 1
                            else:
                                descriptions[DictDescription] = 1
                                totalNumberOfFunctions += 1

                        elif eachDescription in descriptions:
                            descriptions[eachDescription] += 1
                            totalNumberOfFunctions += 1
                        else:
                            descriptions[eachDescription] = 1
                            totalNumberOfFunctions += 1
                        

                subgraphAppearancesFound = function_descriptions['Count of Subgraph Appearances']
                for description, count in subgraphAppearancesFound.items():
                    if description in subgraphAppearances:
                        subgraphAppearances[description] += count
                    else:
                        subgraphAppearances[description] = count

    
    for description in descriptions:
        descriptions[description] = [descriptions[description], round((descriptions[description]/totalNumberOfFunctions), 3)]

    sorted_descriptions = dict(sorted(descriptions.items(), key=lambda x: x[1][0], reverse=True))
    print("----------------------------------------")
    print("Total - Percentage \'Description\'\n")
    for description in sorted_descriptions:
        print(sorted_descriptions[description][0], " - ", sorted_descriptions[description][1], " \'", description.strip(), "\'")
    print("----------------------------------------")

    print("\n\n----------------------------------------")
    print("Total - Subgraph Combinations\n")
    sorted_subgraphAppearances = dict(sorted(subgraphAppearances.items(), key=lambda x: x[1], reverse=True))
    for description in sorted_subgraphAppearances:
        print(sorted_subgraphAppearances[description], " - ", description.strip())
    print("----------------------------------------")

        

exports = [function_description_occurances]