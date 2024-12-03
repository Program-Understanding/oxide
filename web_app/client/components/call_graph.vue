<template>
    <div>
        <div id="network" style="width: 100%; height: 100vh;"></div>
        <LoadingSpinner :visible="loading" />
    </div>
</template>

<script>
import { ref, onMounted, watch } from 'vue';
import { Network } from 'vis-network/standalone/esm/vis-network';
import domtoimage from 'dom-to-image';
import LoadingSpinner from "./LoadingSpinner.vue";

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
    emits: ['update:downloadChart'],
    setup(props, {emit}) {
        const networkInstance = ref(null);
        const loading = ref(true);

        const fetchDataAndPlot = async () => {
            try {
                loading.value = true;

                const url = new URL("http://localhost:8000/api/retrieve");
                url.searchParams.append("selected_module", props.selectedModule);
                url.searchParams.append("selected_collection", props.selectedCollection);

                const response = await fetch(url);
                if (!response.ok) {
                    throw new Error(`HTTP error! status: ${response.status}`);
                }
                const normalData = await response.json();
                console.log('API Response:', normalData);
                const data = normalData[props.oid];

                const container = document.getElementById("network");

                const nodes = [];
                const edges = [];
                const callCounts = {};

                // Nodes
                for (const nodeId in data._node) {
                    callCounts[nodeId] = { incomingCalls: 0, outgoingCalls: 0 };
                    const node = data._node[nodeId];
                    nodes.push({
                        id: nodeId,
                        label: node.label || nodeId, // Use node label if available
                        title: `Node ID: ${nodeId}\nTimes called: ${callCounts[nodeId].incomingCalls}\nCalls made: ${callCounts[nodeId].outgoingCalls}`
                    });
                }

                // Edges
                for (const fromNode in data._adj) {
                    for (const toNode in data._adj[fromNode]) {
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

                const dataForNetwork = { nodes, edges };
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

                networkInstance.value = new Network(container, dataForNetwork, options);
                loading.value = false;

            } catch (error) {
                console.error('Error creating call graph:', error);
            }
        };

        onMounted(() => {
            fetchDataAndPlot();
            emit('update:downloadChart', downloadChart);

        });

        const downloadChart = () => {
            const container = document.getElementById("network");

            // Temporarily set the background to dark
            container.style.backgroundColor = "#333";

            domtoimage.toSvg(container)
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


        watch(() => [props.selectedModule, props.selectedCollection, props.file], () => {
            fetchDataAndPlot();
        });

        return {
            networkInstance,
            loading,
        };
    },
};
</script>

<style scoped>
#network {
    width: 100%;
    height: 100%;
}
</style>