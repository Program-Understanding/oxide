type CytoscapeFactory = any;

let cytoscapeLoader: Promise<CytoscapeFactory> | null = null;

export async function loadCytoscape(): Promise<CytoscapeFactory> {
  if (!cytoscapeLoader) {
    cytoscapeLoader = (async () => {
      await import("hammerjs");
      const [cy, dagreModule] = await Promise.all([
        import("cytoscape"),
        import("cytoscape-dagre"),
      ]);
      cy.default.use(dagreModule.default as any);
      return cy.default;
    })();
  }

  return cytoscapeLoader;
}
