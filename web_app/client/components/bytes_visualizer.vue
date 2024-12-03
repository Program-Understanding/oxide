<template>
    <div class="visualizer-container">
        <canvas id="network"></canvas>
        <div id="infoBox" class="info-box"></div>
        <LoadingSpinner :visible="loading" />
    </div>
</template>

<script>
import { onMounted, ref, watch } from 'vue';
import * as d3 from 'd3';
import { Chart, registerables } from "chart.js";
import LoadingSpinner from "./LoadingSpinner.vue";
Chart.register(...registerables);

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
    setup(props) {
        const loading = ref(true);

        const plotBinary = async (chartData) => {
            const container = document.getElementById("network");
            const infoBox = document.getElementById("infoBox");

            const gridData = JSON.parse(chartData);
            console.log("Grid data:", gridData);

            // Flatten the gridData array
            const flattenedData = gridData.flat();

            // Set up dimensions and canvas
            const width = 1000;
            const rows = gridData.length;
            const cellSize = rows < 200 ? 10 : 5;
            const cols = gridData[0].length;
            const totalHeight = rows * cellSize;

            container.width = width;
            container.height = totalHeight + 50;
            

            // Create a color scale
            const colorScale = d3.scaleSequential(d3.interpolateViridis)
                .domain([0, 255]);

            // Draw the grid of cells
            const ctx = container.getContext("2d");

            flattenedData.forEach((d, i) => {
                const x = (i % cols) * cellSize;
                const y = Math.floor(i / cols) * cellSize;
                ctx.fillStyle = colorScale(d);
                ctx.fillRect(x, y, cellSize, cellSize);
                ctx.strokeStyle = "gray";
                ctx.strokeRect(x, y, cellSize, cellSize);
            });

            container.addEventListener("mousemove", (event) => {
                const rect = container.getBoundingClientRect();
                const x = event.clientX - rect.left;
                const y = event.clientY - rect.top;
                const col = Math.floor(x / cellSize);
                const row = Math.floor(y / cellSize);
                const index = row * cols + col;
                const d = flattenedData[index];

                if (d !== undefined) {
                    const hexValue = d.toString(16).toUpperCase().padStart(2, '0');
                    const binaryValue = d.toString(2).padStart(8, '0');

                    if (infoBox) {
                        infoBox.innerHTML = `
                            <strong>Byte Information</strong><br>
                            Value: ${d}<br>
                            Position: (${row}, ${col})<br>
                            Hex: 0x${hexValue}<br>
                            Binary: ${binaryValue}
                        `;
                    }
                }
            });
        };

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
                const data = await response.json();
                console.log('API Response:', data);

                const chartData = data[props.oid];
                if (!chartData) {
                    console.error(`OID ${props.oid} not found in data`);
                    return;
                }

                plotBinary(chartData);
                loading.value = false;

            } catch (error) {
                console.error('Error fetching data:', error);
            }
        };

        onMounted(() => {
            fetchDataAndPlot();
        });

        watch(() => [props.selectedModule, props.selectedCollection, props.file, props.oid], () => {
            fetchDataAndPlot();
        });

        return { loading, };
    },
};
</script>

<style scoped>
.visualizer-container {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
}

.info-box {
    position: fixed;
    right: 30px;
    top: 30px;
    background-color: white;
    border: 1px solid black;
    padding: 10px;
    border-radius: 5px;
    box-shadow: 0 0 10px rgba(0, 0, 0, 0.5);
    width: 250px;
    height: 200px;
    font-size: x-large;
    color: black;
}
</style>