import { Chart, registerables } from "chart.js";
import { chartInstance } from "../pages/state"; // Ensure collectionFiles is imported
Chart.register(...registerables);

const byteHistogram = (histogramData) => {
    const ctx = document.getElementById("chartCanvas").getContext("2d");

    if (chartInstance.value && typeof chartInstance.value.destroy === "function") {
        chartInstance.value.destroy();
        chartInstance.value = null;
    }

    const values = Object.values(histogramData).sort((a, b) => b - a);
    const maxYValue = Math.floor(values[1] * 1.1);

    chartInstance.value = new Chart(ctx, {
        type: "bar",
        data: {
            labels: Object.keys(histogramData),
            datasets: [
                {
                    label: "Byte Frequency (log scale)",
                    data: Object.values(histogramData),
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
};

export default byteHistogram;