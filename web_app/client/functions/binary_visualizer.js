import * as d3 from 'd3';

const plotBinary = async (chartData) => {
    const container = document.getElementById("network");

    if (!container) {
        console.error("Container element with ID 'network' not found.");
        return;
    }

    // Clear any existing plot
    while (container.firstChild) {
        container.removeChild(container.firstChild);
    }

    const key = Object.keys(chartData)[0];
    const binaryDataString = chartData[key];
    let gridData;

    try {
        gridData = JSON.parse(binaryDataString);
    } catch (error) {
        console.error("Failed to parse binary data string:", error);
        return;
    }

    console.log("Grid data:", gridData);

    
    // Set up dimensions and SVG container
    const width = 1000;
    const rows = gridData.length;
    let cellSize;
    (rows > 200) ? cellSize = 5 : cellSize = 10;
    const cols = gridData[0].length;
    const totalHeight = rows * cellSize;
    

    // Create a scrollable container
    const svg = d3.select(container)
    .append("svg")
    .attr("width", width)
    .attr("height", totalHeight + 50)
    .style("overflow", "auto");


    // Create a color scale
    const colorScale = d3.scaleSequential(d3.interpolateViridis)
    .domain([0, 255]);

    // Create a grid of cells
    const cells = svg.selectAll("rect")
    .data(gridData.flat())
    .enter()
    .append("rect")
    .attr("x", (d, i) => (i % cols) * cellSize)
    .attr("y", (d, i) => Math.floor(i / cols) * cellSize)
    .attr("width", cellSize)
    .attr("height", cellSize)
    .attr("fill", d => colorScale(d))
    .attr("stroke", "gray")
    .on("mouseover", function(event, d) {
        d3.select(this).attr("stroke", "red");
    })
    .on("mouseout", function() {
        d3.select(this).attr("stroke", "gray");
    })
    .on("click", function(event, d) {
        const row = Math.floor(d3.select(this).attr("y") / cellSize);
        const col = Math.floor(d3.select(this).attr("x") / cellSize);
        const hexValue = d.toString(16).toUpperCase().padStart(2, '0');
        const binaryValue = d.toString(2).padStart(8, '0');

        const infoBox = document.getElementById("infoBox");
        if (infoBox) {
            infoBox.innerHTML = `
                <strong>Byte Information</strong><br>
                Value: ${d}<br>
                Position: (${row}, ${col})<br>
                Hex: 0x${hexValue}<br>
                Binary: ${binaryValue}
            `;
        }
    });
};


export default plotBinary;