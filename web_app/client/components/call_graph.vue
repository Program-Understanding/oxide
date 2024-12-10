<template>
    <div class="container">
        <div class="node-list">
            <ul>
                <li v-for="func in functions" :key="func" @click="selectNode(func)">
                    {{ func }}
                </li>
            </ul>
        </div>
        <div id="network" style="width: 100vw; height: 100vh;"></div>
        <LoadingSpinner :visible="loading" />
    </div>
</template>

<script>
import { ref, onMounted, watch } from "vue";
import cytoscape from "cytoscape";
import dagre from "cytoscape-dagre";
import domtoimage from "dom-to-image";
import LoadingSpinner from "./LoadingSpinner.vue";

cytoscape.use(dagre);

export default {
    components: {
        LoadingSpinner,
    },
    props: {
        file: String,
        selectedModule: String,
        selectedCollection: String,
        oid: String,
    },
    emits: ["update:downloadChart"],
    setup(props, { emit }) {
        const networkInstance = ref(null);
        const loading = ref(true);
        const nodeIds = ref([]);
        const functions = ref([]);

        const fetchDataAndPlot = async () => {
            try {
                loading.value = true;

                const url = new URL("http://localhost:8000/api/retrieve");
                url.searchParams.append("selected_module", "control_flow_graph");
                url.searchParams.append(
                    "selected_collection",
                    props.selectedCollection
                );

                const response = await fetch(url);
                if (!response.ok) {
                    throw new Error(`HTTP error! status: ${response.status}`);
                }
                const normalData = await response.json();
                const data = normalData[props.oid];

                console.log(data);

                const container = document.getElementById("network");

                const elements = [];
                const functionCalls = data.function_calls; // ex. {4096 : {called_by : []}, {calls : ["printf"]}}}
                const edges = data.edges; // ex. {"from" : 4096, "to" : 4118}
                const functionToFirstBlock = {};
                const functionBlocks = data.functions;

                functions.value = Object.keys(data["functions"]).filter(
                    (func) => data["functions"][func].blocks.length > 0
                );
                console.log(functions.value);

                // Map functions to their first block ID
                for (const functionName in functionBlocks) {
                    const blocks = data.functions[functionName].blocks;
                    if (blocks.length > 0) {
                        functionToFirstBlock[functionName] = blocks[0];
                        console.log(`Mapped function ${functionName} to first block ID ${blocks[0]}`);
                    }
                }

                // Nodes
                for (const functionName in functionToFirstBlock) {
                    const blockId = functionToFirstBlock[functionName];

                    elements.push({
                        data: {
                            id: blockId,
                            label: `Block ID: ${blockId}\nFunction: ${functionName}`,
                        }
                    });
                    nodeIds.value.push(blockId);
                    console.log(`Added node for function ${functionName} with block ID ${blockId}`);
                }

                console.log(functionToFirstBlock)

                // Ensure all nodes are added before creating edges
                for (let i = 0; i < edges.length; i++) {
                    const edge = edges[i];
                    const fromNode = edge.from;
                    const toNode = edge.to;

                    // Add "from" node if it doesn't already exist and is a function
                    if (!nodeIds.value.includes(fromNode) && !isNaN) {
                        elements.push({
                            data: {
                                id: fromNode,
                                label: `Block ID: ${fromNode}`,
                            }
                        });
                        nodeIds.value.push(fromNode);
                        console.log(`Added node for block ID ${fromNode}`);
                    }

                    // Add "to" node if it doesn't already exist and is a fuction
                    if (!nodeIds.value.includes(toNode) && !isNaN) {
                        elements.push({
                            data: {
                                id: toNode,
                                label: `Block ID: ${toNode}`,
                            }
                        });
                        nodeIds.value.push(toNode);
                        console.log(`Added node for block ID ${toNode}`);
                    }
                }


                // Edges
                for (let i = 0; i < edges.length; i++) {
                    const edge = edges[i];
                    const fromNode = edge.from;
                    const toNode = edge.to;

                    const fromFunction = getFunctionName(fromNode, data.functions);
                    const toFunction = getFunctionName(toNode, data.functions);

                    // Filter out calls from and to the same function
                    if (fromFunction && toFunction && fromFunction === toFunction) {
                        console.log(`Skipped edge from block ID ${fromNode} to block ID ${toNode} (same function)`);
                        continue;
                    }

                    const fromBlockId = functionToFirstBlock[fromFunction] || fromNode;
                    const toBlockId = functionToFirstBlock[toFunction] || toNode;

                    // Check for non-function nodes
                    if (!elements.some(el => el.data.id === fromBlockId)) {
                        console.error(`Error creating call graph: Error: Can not create edge \`edge-${fromBlockId}-${toBlockId}\` with nonexistant source \`${fromBlockId}\``);
                        continue;
                    }
                    if (!elements.some(el => el.data.id === toBlockId)) {
                        console.error(`Error creating call graph: Error: Can not create edge \`edge-${fromBlockId}-${toBlockId}\` with nonexistant target \`${toBlockId}\``);
                        continue;
                    }

                    // Add edge
                    elements.push({
                        data: {
                            id: `edge-${fromBlockId}-${toBlockId}`,
                            source: fromBlockId,
                            target: toBlockId,
                        }
                    });
                    console.log(`Added edge from block ID ${fromBlockId} to block ID ${toBlockId}`);
                }

                // Helper function to get function name by block ID
                function getFunctionName(blockId, functions) {
                    for (const functionName in functions) {
                        if (functions[functionName].blocks.includes(blockId)) {
                            return functionName;
                        }
                    }
                    return blockId;
                }
                const cy = cytoscape({
                    container: container,
                    elements: elements,
                    style: [
                        {
                            selector: "node",
                            style: {
                                "background-color": "#1f77b4",
                                label: "data(label)",
                                "text-valign": "center",
                                "text-justification": "left",
                                color: "#fff",
                                shape: "roundrectangle",
                                width: "label",
                                height: "label",
                                padding: "10px",
                                "text-wrap": "wrap",
                                "text-max-width": "300px",
                                "font-family": "monospace",
                                "font-size": "12px",
                                "min-zoomed-font-size": 12,
                            },
                        },
                        {
                            selector: "edge",
                            style: {
                                width: 2,
                                "line-color": "#9dbaea",
                                "target-arrow-color": "#9dbaea",
                                "target-arrow-shape": "triangle",
                                "arrow-scale": 1.5,
                                "curve-style": "bezier",
                            },
                        },
                        {
                            selector: '.highlighted',
                            style: {
                                'background-color': 'salmon',
                                'line-color': 'salmon',
                                'target-arrow-color': 'salmon',
                                'transition-property': 'background-color, line-color, target-arrow-color',
                                'transition-duration': '0.5s'
                            }
                        },
                    ],
                    layout: {
                        name: "dagre",
                        fit: true,
                        padding: 10,
                    },
                    minZoom: 0.1, // Minimum zoom level
                    maxZoom: 2, // Maximum zoom level
                    zoom: 1, // Initial zoom level
                    wheelSensitivity: 0.2,
                });

                networkInstance.value = cy;
                loading.value = false;
            } catch (error) {
                console.error("Error creating call graph:", error);
                loading.value = false;
            }
        };

        const selectNode = (functionName) => {
            const cy = networkInstance.value;
            if (cy) {
                // Find the node with the specified function name
                const node = cy.nodes().filter(`[label *= "Function: ${functionName}"]`);
                if (node.length > 0) {
                    // Reset previous highlights
                    cy.elements().removeClass('highlighted');

                    // Highlight connected edges and nodes
                    const connectedEdges = node.connectedEdges();
                    connectedEdges.addClass('highlighted');
                    connectedEdges.connectedNodes().addClass('highlighted');

                    // Center the view on the selected node
                    node.removeClass('highlighted');
                    cy.center(node);
                } else {
                    console.warn(`Node with function name ${functionName} not found.`);
                }
            }
        };

        onMounted(() => {
            fetchDataAndPlot();
            emit("update:downloadChart", downloadChart);
        });

        const downloadChart = () => {
            const container = document.getElementById("network");

            // Temporarily set the background to dark
            container.style.backgroundColor = "#333";

            domtoimage
                .toSvg(container, {
                    width: container.clientWidth * scale,
                    height: container.clientHeight * scale,
                    style: {
                        transform: `scale(${scale})`,
                        transformOrigin: "top left",
                        width: `${container.clientWidth}px`,
                        height: `${container.clientHeight}px`,
                    },
                })
                .then((dataUrl) => {
                    // Reset the background color
                    container.style.backgroundColor = "";

                    const link = document.createElement("a");
                    link.href = dataUrl;
                    link.download = "CallGraph.svg";
                    link.click();
                })
                .catch((error) => {
                    console.error("Error generating SVG:", error);
                    // Reset the background color in case of error
                    container.style.backgroundColor = "";
                });
        };

        watch(
            () => [props.selectedModule, props.selectedCollection, props.file],
            () => {
                fetchDataAndPlot();
            }
        );

        return {
            networkInstance,
            loading,
            nodeIds,
            selectNode,
            functions,
        };
    },
};
</script>

<style scoped>
#network {
    width: 100vw;
    height: 100vh;
    position: absolute;
    z-index: 1;
}

.container {
    display: flex;
    flex-direction: row;
    align-items: flex-start;
    justify-content: center;
    width: 100vw;
    height: 100vh;
}

.node-list {
    width: 200px;
    margin-right: 20px;
    max-height: 100%;
    overflow-y: auto;
    border: 1px solid #ccc;
    border-radius: 5px;
    padding: 10px;
    background-color: rgba(0, 0, 0, 0.5);
    box-shadow: 0 0 10px rgba(0, 0, 0, 0.1);
    z-index: 2;
    position: absolute;
    top: 0;
    left: 0;
}

.node-list ul {
    list-style-type: none;
    padding: 0;
    margin: 0;
}

.node-list li {
    cursor: pointer;
    padding: 5px;
    border-bottom: 1px solid #ccc;
}

.node-list li:hover {
    background: salmon;
}
</style>