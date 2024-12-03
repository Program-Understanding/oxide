import { MatrixController, MatrixElement } from 'chartjs-chart-matrix';
import { Chart, registerables } from "chart.js";
import { selectedModule, selectedCollection, chartInstance, responseData, tableData, collectionFiles } from "../pages/state"; // Ensure collectionFiles is imported
Chart.register(MatrixController, MatrixElement);
Chart.register(...registerables);


const ngramsHeatmap = (histogramData) => {
    const ctx = document.getElementById("chartCanvas")?.getContext("2d");

    if (chartInstance.value) {
        chartInstance.value.destroy();
    }

    const compareNGrams = (a, b) => {
        const aParts = a[0].split(',').map(Number);
        const bParts = b[0].split(',').map(Number);

        for (let i = 0; i < Math.max(aParts.length, bParts.length); i++) {
            const aPart = aParts[i] || 0;
            const bPart = bParts[i] || 0;

            if (aPart !== bPart) {
                return aPart - bPart;
            }
        }
        return 0;
    };

    // Convert histogramData to an array of [key, value] pairs
    const dataArray = Object.entries(histogramData);

    // Sort the data by n-gram keys to maintain order
    dataArray.sort(compareNGrams);

    // Calculate the number of columns and rows for a more square-like grid
    const totalItems = dataArray.length;
    const numColumns = Math.ceil(Math.sqrt(totalItems));
    const numRows = Math.ceil(totalItems / numColumns);

    const data = dataArray.map((item, index) => ({
        x: index % numColumns, // Adjust for grid layout
        y: Math.floor(index / numColumns), // Adjust for grid layout
        v: item[1]
    }));

    // Calculate the maximum value for color scaling from the data excluding the first point
    const maxValue = Math.max(...data.slice(1).map(d => d.v));

    chartInstance.value = new Chart(ctx, {
        type: 'matrix',
        data: {
            datasets: [{
                label: 'Byte Frequency',
                data: data,
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
                    title: {
                        display: false,
                        text: 'Byte n-grams'
                    },
                    ticks: {
                        display: false
                    }
                },
                y: {
                    title: {
                        display: true,
                        text: 'Frequency'
                    },
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
                            return `Byte n-gram: ${label}, Frequency: ${value}`;
                        }
                    }
                },
                legend: {
                    display: false
                }
            }
        }
    });
};

export default ngramsHeatmap;