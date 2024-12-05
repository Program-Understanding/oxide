<template>
    <div id="container" class="flex flex-col min-h-screen h-screen bg-zinc-900"> 
        <Sidebar>
            <div id="currentFile">Current file: {{ selectedFile }}</div>
            <button @click="togglePopup">Select New Chart/File</button>
            <button @click="downloadChart">Download Chart</button>
        </Sidebar>

        <ChartPopup :chartModules="chartModules" :collections="collections"
            @selectionConfirmed="handleSelectionConfirmed" v-if="showPopup" />
        <component :is="currentChartComponent" :file="selectedFile" :selectedModule="selectedModule"
            :selectedCollection="selectedCollection" :oid="selectedOid" v-if="currentChartComponent"
            @update:downloadChart="setDownloadChartFunction" style="padding-right: 100px;"></component>
    </div>
</template>

<script setup>
import { ref, onMounted } from 'vue';
import ChartPopup from './components/chart_popup.vue';
import Sidebar from './components/sidebar.vue';
import EntropyChart from './components/EntropyChart.vue';
import ByteHistogram from './components/byte_histogram.vue';
import NgramsHeatmap from './components/byte_ngrams.vue';
import OpcodeHistogram from './components/opcode_histogram.vue';
import OpcodeNgrams from './components/opcode_ngrams.vue';
import CallGraph from './components/call_graph.vue';
import FlowGraph from './components/control_flow_graph.vue';
import BytesVisualizer from './components/bytes_visualizer.vue';

const chartModules = ["entropy_graph", "byte_histogram", "byte_ngrams", "opcode_histogram", "opcode_ngrams", "call_graph", "control_flow_graph", "binary_visualizer"];
const collections = ref([]);
const selectedFile = ref('');
const selectedModule = ref('');
const selectedCollection = ref('');
const selectedOid = ref('');
const currentChartComponent = shallowRef(null);
const showPopup = ref(true);
const downloadChartFunction = ref(null);

onMounted(async () => {
    const [collectionsData] = await Promise.all([
        fetch("http://localhost:8000/api/collections/").then((res) => res.json()),
    ]);
    collections.value = collectionsData;
});

const handleSelectionConfirmed = ({ chartType, collection, file, oid }) => {
    console.log(`Selected Chart Type: ${chartType}, Collection: ${collection}, File: ${file}, OID: ${oid}`);
    togglePopup();
    selectedFile.value = file;
    selectedModule.value = chartType;
    selectedCollection.value = collection;
    selectedOid.value = oid;

    switch (chartType) {
        case "entropy_graph":
            currentChartComponent.value = EntropyChart;
            break;
        case "byte_histogram":
            currentChartComponent.value = ByteHistogram;
            break;
        case "byte_ngrams":
            currentChartComponent.value = NgramsHeatmap;
            break;
        case "opcode_histogram":
            currentChartComponent.value = OpcodeHistogram;
            break;
        case "opcode_ngrams":
            currentChartComponent.value = OpcodeNgrams;
            break;
        case "call_graph":
            currentChartComponent.value = CallGraph;
            break;
        case "control_flow_graph":
            currentChartComponent.value = FlowGraph;
            break;
        case "binary_visualizer":
            currentChartComponent.value = BytesVisualizer;
            break;
        default:
            currentChartComponent.value = null;
            break;
    }
};

const togglePopup = () => {
    showPopup.value = !showPopup.value;
    currentChartComponent.value = null;
};

const setDownloadChartFunction = (downloadChart) => {
    downloadChartFunction.value = downloadChart;
};

const downloadChart = () => {
    if (downloadChartFunction.value) {
        downloadChartFunction.value();
    } else {
        console.error("No chart download function available");
    }
};
</script>

<style>
@import url("~/assets/css/base.css");

.ChartPopup {
    position: fixed;
    right: 5%;
    top: 50%;
    width: 500px;
    border: 5px solid black;
    padding: 10px;
    box-shadow: 0 0 10px rgba(0, 0, 0, 0.1);
    z-index: 1000;
}

button {
    margin: 10px 0;
    padding: 10px 20px;
    background-color: #444;
    color: white;
    border: none;
    cursor: pointer;
}

button:hover {
    background-color: #555;
}

#currentFile {
    margin-bottom: 20px;
    font-weight: bold;
    font-size: 22px;
    word-wrap: break-word;
    border-bottom: 2px solid salmon;
}
</style>