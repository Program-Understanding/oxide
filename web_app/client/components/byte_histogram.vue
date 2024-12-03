<template>
    <div>
        <canvas id="chartCanvas"></canvas>
        <LoadingSpinner :visible="loading" />
    </div>
</template>

<script>
import { onMounted, ref, watch } from 'vue';
import { Chart, registerables } from 'chart.js';
import LoadingSpinner from "./LoadingSpinner.vue";
import domtoimage from 'dom-to-image';
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

                chartInstance.value = new Chart(ctx, {
                    type: "bar",
                    data: {
                        labels: Object.keys(data),
                        datasets: [
                            {
                                label: "Byte Frequency (log scale)",
                                data: Object.values(data),
                                backgroundColor: "rgba(75, 192, 192, 0.2)",
                                borderColor: "rgba(75, 192, 192, 1)",
                                borderWidth: 1,
                            },
                        ],
                    },
                    options: {
                        scales: {
                            y: {
                                type: 'logarithmic',
                                beginAtZero: true,
                                ticks: {
                                    callback: function (value, index, values) {
                                        if (value === 1 || value === 10 || value === 100 || value === 1000 || value === 10000) {
                                            return value;
                                        }
                                        return null;
                                    }
                                }
                            },
                            x: {
                                ticks: {
                                    font: {
                                        size: 12
                                    },
                                    color: 'white'
                                }
                            },
                        },
                        plugins: {
                            tooltip: {
                                callbacks: {
                                    label: function (context) {
                                        const index = context.dataIndex;
                                        const actualValue = context.dataset.data[index];
                                        return `Byte Freqency: ${actualValue}`;
                                    }
                                }
                            },
                            legend: {
                                labels: {
                                    font: {
                                        size: 20
                                    }
                                }
                            }
                        }
                    },
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
                    link.download = "ByteHistogram.svg";
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