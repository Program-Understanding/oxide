<template>
    <div>
        <canvas id="chartCanvas"></canvas>
        <LoadingSpinner :visible="loading" />
    </div>
</template>

<script>
import { onMounted, ref, watch } from 'vue';
import { MatrixController, MatrixElement } from 'chartjs-chart-matrix';
import { Chart, registerables } from 'chart.js';
import domtoimage from 'dom-to-image';
import LoadingSpinner from "./LoadingSpinner.vue";
Chart.register(MatrixController, MatrixElement);
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
    emits: ['update:downloadChart'],
    setup(props, {emit}) {
        const chartInstance = ref(null);
        const loading = ref(true);

        const fetchDataAndPlot = async () => {
            try {
                loading.value = true;

                const url = new URL("http://localhost:8000/api/retrieve");
                url.searchParams.append("selected_module", props.selectedModule);
                url.searchParams.append("selected_oid", props.oid);

                const response = await fetch(url);
                if (!response.ok) {
                    throw new Error(`HTTP error! status: ${response.status}`);
                }
                const data = await response.json();
                console.log('API Response:', data);

                const ctx = document.getElementById('chartCanvas').getContext('2d');

                const dataArray = Object.entries(data);

                const totalItems = dataArray.length;
                const numColumns = Math.ceil(Math.sqrt(totalItems));
                const numRows = Math.ceil(totalItems / numColumns);

                const heatmapData = dataArray.map((item, index) => ({
                    x: index % numColumns, // Adjust for grid layout
                    y: Math.floor(index / numColumns), // Adjust for grid layout
                    v: item[1]
                }));

                const maxValue = Math.max(...heatmapData.slice(1).map(d => d.v));

                chartInstance.value = new Chart(ctx, {
                    type: 'matrix',
                    data: {
                        datasets: [{
                            label: 'Opcode Frequency',
                            data: heatmapData,
                            backgroundColor: (context) => {
                                const value = context.dataset.data[context.dataIndex].v;
                                const logValue = Math.log(value + 1); // Apply logarithmic scale
                                const logMaxValue = Math.log(maxValue + 1);
                                const alpha = logValue / logMaxValue;
                                const r = Math.floor(255 * alpha);
                                const g = Math.floor(255 * (1 - alpha));
                                return `rgba(${r}, ${g}, 0, 1)`;
                            },
                            borderColor: 'rgba(0, 0, 0, 0.1)',
                            borderWidth: 1,
                            width: (context) => {
                                const chartArea = context.chart.chartArea || { width: 1 };
                                return (chartArea.width) / numColumns;
                            },
                            height: (context) => {
                                const chartArea = context.chart.chartArea || { height: 1 };
                                return (chartArea.height) / numRows;
                            },
                        }]
                    },
                    options: {
                        layout: {
                            padding: {
                                top: 30,
                            }
                        },
                        scales: {
                            x: {
                                ticks: {
                                    display: false
                                }
                            },
                            y: {
                                ticks: {
                                    display: false
                                }
                            }
                        },
                        plugins: {
                            tooltip: {
                                mode: 'nearest',
                                position: 'average',
                                callbacks: {
                                    label: function (context) {
                                        const index = context.dataIndex;
                                        const label = dataArray[index][0];
                                        const value = context.raw.v;
                                        return `Opcode n-gram: ${label}, Frequency: ${value}`;
                                    }
                                }
                            },
                            legend: {
                                display: false
                            }
                        }
                    }
                });
                loading.value = false;
            } catch (error) {
                console.error('Error fetching data:', error);
            }
        };

        onMounted(() => {
            fetchDataAndPlot();
            emit('update:downloadChart', downloadChart);
        });

        const downloadChart = () => {
            const canvas = document.getElementById("chartCanvas");
            const tempCanvas = document.createElement("canvas");
            const tempCtx = tempCanvas.getContext("2d");

            tempCanvas.width = canvas.width;
            tempCanvas.height = canvas.height;

            // Draw dark background
            tempCtx.fillStyle = "#333"; // Dark background color
            tempCtx.fillRect(0, 0, tempCanvas.width, tempCanvas.height);

            // Draw the original canvas content on top of the dark background
            tempCtx.drawImage(canvas, 0, 0);

            domtoimage.toSvg(tempCanvas)
                .then((dataUrl) => {
                    const link = document.createElement("a");
                    link.href = dataUrl;
                    link.download = "OpcodeNgrams.svg";
                    link.click();
                })
                .catch((error) => {
                    console.error("Error generating SVG:", error);
                });
        };

        watch(() => [props.selectedModule, props.selectedCollection, props.file], () => {
            fetchDataAndPlot();
        });

        return {
            chartInstance,
            loading,
        };
    },
};
</script>

<style scoped>
canvas {
    max-width: 100%;
}
</style>