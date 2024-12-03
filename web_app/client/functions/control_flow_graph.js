import cytoscape from "cytoscape";
import dagre from "cytoscape-dagre";


const flowGraph = async (graphData) => {

    while (document.getElementById('network').firstChild) {
        document.getElementById('network').removeChild(container.firstChild);
    }

    cytoscape.use(dagre);

    const elements = [];
    const firstKey = Object.keys(graphData)[0];
    const data = graphData[firstKey];

    // Create a set of node IDs
    const nodeIds = new Set(data.nodes.map(node => node.id));

    // Add nodes to elements
    data.nodes.forEach(node => {
        const instructions = node.instructions.map(instr => {
            if (Array.isArray(instr)) {
                // Handle array format instructions
                return `${instr[0]}: ${instr[1]}`;
            } else {
                // Handle object format instructions
                return `Name: ${instr.name}\n` +
                       `Vaddr: ${instr.vaddr}\n` +
                       `Params: ${(instr.params || []).join(', ')}\n` +
                       `RetType: ${instr.retType}\n` +
                       `Signature: ${instr.signature}\n` +
                       `Returning: ${instr.returning}`;
            }
        }).join('\n\n');

        elements.push({
            data: {
                id: node.id,
                label: `Block ${node.id}\n${instructions}`,
                instructions: instructions
            }
        });
    });

    // Add edges to elements, only if both source and target nodes exist
    data.edges.forEach(edge => {
        if (nodeIds.has(edge.from) && nodeIds.has(edge.to)) {
            elements.push({
                data: {
                    source: edge.from,
                    target: edge.to
                }
            });
        }
    });

    // Initialize Cytoscape
    const cy = cytoscape({
        
        container: document.getElementById('network'),
        
        elements: elements,
        style: [
            {
                selector: 'node',
                style: {
                    'background-color': '#1f77b4',
                    'label': 'data(label)',
                    'text-valign': 'center',
                    'color': '#fff',
                    'shape': 'roundrectangle',
                    'width': 'label',
                    'height': 'label',
                    'padding': '10px',
                    'text-wrap': 'wrap',
                    'text-max-width': '200px',
                    'font-family': 'monospace',
                    'font-size': '10px'
                }
            },
            {
                selector: 'edge',
                style: {
                    'width': 2,
                    'line-color': '#9dbaea',
                    'target-arrow-color': '#9dbaea',
                    'target-arrow-shape': 'triangle',
                    'arrow-scale': 1.5, // Optional: Adjust the size of the arrow
                    'curve-style': 'bezier' // Optional: Make the edges curved
                }
            }
        ],
        layout: {
            name: 'dagre', // Use a layout that respects the container's dimensions
            fit: true, // Fit the graph to the container
            padding: 10 // Optional: Padding around the graph
        }
    });
};

export default flowGraph;