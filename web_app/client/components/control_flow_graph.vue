<template>
    <div class="visualizer-container">
        <div class="function-list">
            <ul>
                <li v-for="func in functions" :key="func" @click="selectFunction(func)"
                    :class="{ selected: func == selectedFunction }">
                    {{ func }}
                </li>
            </ul>
        </div>
        <div id="network"></div>
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
        const functions = ref([]);
        const selectedFunction = ref(null);
        const graphData = ref({});
        const loading = ref(true);
        const dropdownVisible = ref(false);
        const showControlFlowGraph = ref(true);
        const showCallGraph = ref(false);

        const plotFlowGraph = async (func) => {
            const container = document.getElementById("network");
            if (!container) {
                console.error("Container element with ID 'network' not found.");
                return;
            }
            // Clear any existing plot
            while (container.firstChild) {
                container.removeChild(container.firstChild);
            }

            const elements = [];
            const data = graphData.value;
            console.log(data);

            // Get the blocks and edges related to the selected function
            const functionBlocks = data.functions[func].blocks; // ex. {"_start": [4800, 4846]}
            const blockCalls = data.block_calls; // ex. {4096 : {called_by : [5040]}, {calls : [4116, 4118]}}
            const functionCalls = data.function_calls; // ex. {4096 : {called_by : []}, {calls : ["printf"]}}}
            const nodes = data.nodes; // ex. {"block id" : 4116, {"instructions" : [4096, "endbr64"]}}
            const edges = data.edges; // ex. {"from" : 4096, "to" : 4118}

            // Create a set of node IDs
            const nodeIds = new Set();

            // Create a set to track unique edges
            const edgeSet = new Set();

            // Add nodes to elements
            functionBlocks.forEach((blockId) => {
                const node = nodes.find((node) => node["block id"] === blockId);
                if (node) {
                    const instructions = node.instructions
                        .map((instr) => {
                            return `${instr[0]}: ${instr[1]}`;
                        })
                        .join("\n\n");

                    // Find the function name for the block
                    const functionName = Object.keys(data.functions).find((fn) =>
                        data.functions[fn].blocks.includes(blockId)
                    );

                    elements.push({
                        data: {
                            id: node["block id"],
                            label: `Block ${node["block id"]}\n\n${instructions}`,
                            instructions: instructions,
                        },
                    });
                    nodeIds.add(node["block id"]);
                }
            });

            if (showControlFlowGraph.value) {
                // Add edges for blocks within the function
                edges.forEach((edge) => {
                    if (nodeIds.has(edge.from) && nodeIds.has(edge.to) && Number.isInteger(edge.to)) {
                        const edgeKey = `${edge.from}-${edge.to}`;
                        if (!edgeSet.has(edgeKey)) {
                            elements.push({
                                data: {
                                    source: edge.from,
                                    target: edge.to,
                                },
                            });
                            edgeSet.add(edgeKey);
                        }
                    }
                });
            }

            console.log("Elements for Cytoscape:", elements);

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

            loading.value = false;
        };

        const fetchDataAndPlot = async () => {
            try {
                loading.value = true;
                const url = new URL("http://localhost:8000/api/retrieve");
                url.searchParams.append("selected_module", props.selectedModule);
                url.searchParams.append(
                    "selected_collection",
                    props.selectedCollection
                );

                const response = await fetch(url);
                if (!response.ok) {
                    throw new Error(`HTTP error! status: ${response.status}`);
                }
                const data = await response.json();
                console.log("API Response:", data);

                const graphDataResponse = data[props.oid];
                if (!graphDataResponse) {
                    console.error(response);
                    return;
                }

                // Store the list of functions and graph data
                functions.value = Object.keys(graphDataResponse["functions"]).filter(
                    (func) => graphDataResponse["functions"][func].blocks.length > 0
                );
                graphData.value = graphDataResponse;

                // Plot the first function by default
                if (functions.value.length > 0) {
                    selectedFunction.value = functions.value[0];
                    plotFlowGraph(selectedFunction.value);
                }
            } catch (error) {
                console.error("Error fetching data:", error);
                loading.value = false;
            }
        };

        const selectFunction = (func) => {
            selectedFunction.value = func;
            plotFlowGraph(func);
        };

        onMounted(() => {
            fetchDataAndPlot();
            emit("update:downloadChart", downloadChart);
        });

        const downloadChart = () => {
            const container = document.getElementById("network");

            container.style.backgroundColor = "#333";

            const scale = 3;

            domtoimage
                .toSvg(container, {
                    width: container.clientWidth * scale,
                    height: container.clientHeight * scale,
                    style: {
                        transform: `scale(${scale})`,
                        transformOrigin: 'top left',
                        width: `${container.clientWidth}px`,
                        height: `${container.clientHeight}px`,
                    },
                })
                .then((dataUrl) => {
                    // Reset the background color
                    container.style.backgroundColor = "";

                    const link = document.createElement("a");
                    link.href = dataUrl;
                    link.download = selectedFunction.value + ".svg";
                    link.click();
                })
                .catch((error) => {
                    console.error("Error generating SVG:", error);
                    container.style.backgroundColor = "";
                });
        };

        watch(
            () => [
                props.selectedModule,
                props.selectedCollection,
                props.file,
                props.oid,
            ],
            () => {
                fetchDataAndPlot();
            }
        );

        return {
            functions,
            selectedFunction,
            selectFunction,
            plotFlowGraph,
            loading,
            showControlFlowGraph,
        };
    },
};
</script>

<style scoped>
.visualizer-container {
    display: flex;
    flex-direction: row;
    align-items: flex-start;
    justify-content: center;
    width: 100%;
    height: 100%;
}

.function-list {
    width: 200px;
    margin-right: 20px;
    max-height: 100%;
    overflow-y: auto;
    border: 1px solid #ccc;
    border-radius: 5px;
    padding: 10px;
    box-shadow: 0 0 10px rgba(0, 0, 0, 0.1);
}

.function-list li.selected {
    background: salmon;
}

#network {
    flex-grow: 1;
    width: 100%;
    height: 100%;
}
</style>
