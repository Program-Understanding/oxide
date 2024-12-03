import { MatrixController, MatrixElement } from 'chartjs-chart-matrix';
import { Chart, registerables } from "chart.js";
import { selectedModule, selectedCollection, chartInstance, responseData, tableData, collectionFiles } from "../pages/state";
Chart.register(MatrixController, MatrixElement);
Chart.register(...registerables);


const opcodeNgramsHeatmap = (histogramData) => {
    const ctx = document.getElementById("chartCanvas")?.getContext("2d");

    if (chartInstance.value && typeof chartInstance.value.destroy === "function") {
        chartInstance.value.destroy();
        chartInstance.value = null;
    }


    // Convert histogramData to an array of [key, value] pairs
    const dataArray = Object.entries(histogramData);

    // Sort the data by n-gram keys to maintain order

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
                label: 'Opcode Frequency',
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
                        text: 'Opcode n-grams'
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
};

export default opcodeNgramsHeatmap;