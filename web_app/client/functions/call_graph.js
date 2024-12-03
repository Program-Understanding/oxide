import { ref } from "vue";
import { Network } from "vis-network/standalone/esm/vis-network";
import { chartInstance, collectionFiles } from "../pages/state";

const networkInstance = ref(null);

const callGraph = async (graphData) => {
    if (networkInstance.value) {
        networkInstance.value = null;
    }

    try {
        const nodes = [];
        const edges = [];
        const callCounts = {};


        // Nodes
        for (const nodeId in graphData._node) {
            callCounts[nodeId] = { incomingCalls: 0, outgoingCalls: 0 };
            const node = graphData._node[nodeId];
            nodes.push({
                id: nodeId,
                label: node.label || nodeId, // Use node label if available
                title: `Node ID: ${nodeId}\nTimes called: ${callCounts[nodeId].incomingCalls}\nCalls made: ${callCounts[nodeId].outgoingCalls}`
            });
        }

        // Edges
        for (const fromNode in graphData._adj) {
            for (const toNode in graphData._adj[fromNode]) {
                edges.push({ from: fromNode, to: toNode });
                // Increment the call counters
                callCounts[fromNode].outgoingCalls += 1;
                callCounts[toNode].incomingCalls += 1;
            }
        }

        // Update nodes with call counts
        nodes.forEach(node => {
            const nodeId = node.id;
            node.title = `Node ID: ${nodeId}\nLabel: ${node.label}\nTimes called: ${callCounts[nodeId].incomingCalls}\nCalls made: ${callCounts[nodeId].outgoingCalls}`;
        });


        // Log nodes and edges
        console.log("Nodes:", nodes);
        console.log("Edges:", edges);

        // Render the graph
        const container = document.getElementById("network");
        if (!container) {
            console.error("Container element not found");
            return;
        }

        const data = { nodes, edges };
        const options = {
            nodes: {
                shape: 'dot',
                size: 16,
                font: {
                    size: 32,
                    color: '#ffffff'
                },
                borderWidth: 2
            },
            edges: {
                width: 2,
                font: {
                    size: 12,
                    align: 'middle'
                },
                arrows: {
                    to: { enabled: true, scaleFactor: 1.2 }
                }
            },
            layout: {
                hierarchical: {
                    direction: 'UD',
                    sortMethod: 'directed', // Sort by directed edges
                    levelSeparation: 150, // Adjust level separation
                    nodeSpacing: 200 // Adjust node spacing
                }
            },
            physics: {
                enabled: true,
                stabilization: {
                    iterations: 200,
                },
            },
            interaction: {
                keyboard: true,
                tooltipDelay: 200
            }
        };

        networkInstance.value = new Network(container, data, options);


    } catch (error) {
        console.error("Error creating call graph:", error);
    }

    return networkInstance;
};

const callGraphModule = (data, file) => {
    const keys = Object.keys(collectionFiles.value);
    let oid = null;
    console.log("All keys in collectionFiles.value:", keys);

    // Check if the key exists
    let key = file;
    if (keys.includes(key)) {
        oid = collectionFiles.value[key];
        console.log(`OID for key ${key}:`, oid);
    } else {
        console.error(`Key ${key} not found in collectionFiles.value`);
    }

    // Remove the $ character
    oid = oid.toString();
    if (oid.startsWith("$")) {
        oid = oid.substring(1);
    }
    console.log(`Sliced OID: ${oid}`);

    // Check if oid exists in data
    if (data.hasOwnProperty(oid)) {
        console.log(data[oid]);

        if (
            typeof data[oid] === "object" &&
            data[oid] !== null &&
            data[oid].constructor.name === "Proxy"
        ) {
            data[oid] = Reflect.get(data[oid], "target");
        }
        let graphData = data[oid];

        callGraph(graphData);

    } else {
        console.error(`OID ${oid} not found in data`);
    }
    return;
};

export default callGraphModule;