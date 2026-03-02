"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { loadCytoscape } from "./cytoscape-loader";
import { downloadDataUrl, normalizeCallGraphData } from "./utils";
import type { RendererDataProps } from "./types";

type CytoscapeCore = any;
type CytoscapeElementDefinition = any;

export function CallGraphRenderer({ data }: RendererDataProps) {
  const containerRef = useRef<HTMLDivElement | null>(null);
  const cyRef = useRef<CytoscapeCore | null>(null);
  const [selectedNode, setSelectedNode] = useState<string>("");
  const graph = useMemo(() => normalizeCallGraphData(data), [data]);
  const functionList = useMemo(
    () => [...graph.nodes].sort((a, b) => a.functionName.localeCompare(b.functionName)),
    [graph.nodes],
  );

  const highlightSelectedNode = (nodeId: string) => {
    const cy = cyRef.current;
    if (!cy) return;

    cy.elements().removeClass("selected-node highlighted-in highlighted-out highlighted-edge-in highlighted-edge-out");
    const node = cy.$id(nodeId);
    if (!node || node.empty()) return;

    const incomingNodes = node.incomers("node");
    const outgoingNodes = node.outgoers("node");
    const incomingEdges = node.incomers("edge");
    const outgoingEdges = node.outgoers("edge");

    node.addClass("selected-node");
    incomingNodes.addClass("highlighted-in");
    outgoingNodes.addClass("highlighted-out");
    incomingEdges.addClass("highlighted-edge-in");
    outgoingEdges.addClass("highlighted-edge-out");

    cy.center(node);
  };

  useEffect(() => {
    if (!containerRef.current) return;
    let cancelled = false;

    const nodes = graph.nodes.map((node) => ({
      data: {
        id: node.id,
        blockId: node.blockId,
        functionName: node.functionName,
        label:
          node.blockId !== null
            ? `Block ID: ${node.blockId}\nFunction: ${node.functionName}`
            : `Function: ${node.functionName}`,
      },
    }));
    const edges = graph.edges.map((edge) => ({
      data: { id: edge.id, source: edge.source, target: edge.target },
    }));

    void loadCytoscape().then((cytoscapeFactory) => {
      if (cancelled || !containerRef.current) return;

      cyRef.current?.destroy();
      cyRef.current = cytoscapeFactory({
        container: containerRef.current,
        elements: [...nodes, ...edges] as CytoscapeElementDefinition[],
        style: [
          {
            selector: "node",
            style: {
              "background-color": "#0284c7",
              label: "data(label)",
              color: "#e4e4e7",
              shape: "rectangle",
              width: "label",
              height: "label",
              padding: "8px",
              "font-size": 10,
              "font-family": "monospace",
              "text-wrap": "wrap",
              "text-max-width": 220,
              "text-halign": "center",
              "text-valign": "center",
            },
          },
          { selector: "edge", style: { width: 1.5, "line-color": "#52525b", "target-arrow-color": "#52525b", "target-arrow-shape": "triangle", "curve-style": "bezier" } },
          { selector: ".selected-node", style: { "background-color": "#f59e0b", color: "#f8fafc", "z-index": 999 } },
          { selector: ".highlighted-in", style: { "background-color": "#22c55e" } },
          { selector: ".highlighted-out", style: { "background-color": "#a855f7" } },
          { selector: ".highlighted-edge-in", style: { "line-color": "#22c55e", "target-arrow-color": "#22c55e", width: 2.5 } },
          { selector: ".highlighted-edge-out", style: { "line-color": "#a855f7", "target-arrow-color": "#a855f7", width: 2.5 } },
        ],
        layout: { name: "dagre" },
        minZoom: 0.1,
        maxZoom: 5,
        wheelSensitivity: 0.2,
      });

      cyRef.current.on("tap", "node", (event: any) => {
        const nodeId = event.target.id();
        setSelectedNode(nodeId);
        highlightSelectedNode(nodeId);
      });

      cyRef.current.fit(undefined, 20);
    });

    return () => {
      cancelled = true;
      cyRef.current?.destroy();
      cyRef.current = null;
    };
  }, [graph]);

  useEffect(() => {
    if (!selectedNode) return;
    highlightSelectedNode(selectedNode);
  }, [selectedNode]);

  if (graph.nodes.length === 0) return <p className="text-sm text-zinc-400">No call graph data available.</p>;

  const selectedNodeData = graph.nodes.find((node) => node.id === selectedNode);

  return (
    <div className="space-y-3">
      <div className="flex gap-2">
        <button className="rounded bg-zinc-800 px-3 py-1 text-xs" onClick={() => cyRef.current?.fit()}>Fit graph</button>
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs"
          onClick={() => {
            const png = cyRef.current?.png({ bg: "#09090b", full: true, scale: 2 });
            if (png) downloadDataUrl(png, "call_graph.png");
          }}
        >
          Export PNG
        </button>
      </div>
      <div className="grid grid-cols-1 gap-3 lg:grid-cols-[16rem_minmax(0,1fr)]">
        <div className="rounded border border-zinc-800 bg-zinc-900">
          <div className="border-b border-zinc-800 px-3 py-2 text-xs font-medium text-zinc-300">
            Functions ({functionList.length})
          </div>
          <ul className="max-h-[34rem] overflow-y-auto px-2 py-2 text-sm">
            {functionList.map((node) => (
              <li key={node.id}>
                <button
                  className={`w-full truncate rounded px-2 py-1 text-left ${
                    selectedNode === node.id ? "bg-sky-900/50 text-sky-200" : "text-zinc-300 hover:bg-zinc-800"
                  }`}
                  onClick={() => {
                    setSelectedNode(node.id);
                    highlightSelectedNode(node.id);
                  }}
                  title={node.functionName}
                >
                  {node.functionName}
                </button>
              </li>
            ))}
          </ul>
        </div>
        <div ref={containerRef} className="h-[34rem] w-full rounded border border-zinc-800 bg-zinc-900" />
      </div>
      <p className="text-xs text-zinc-400">Nodes: {graph.nodes.length} · Edges: {graph.edges.length}</p>
      {selectedNode ? (
        <p className="text-xs text-zinc-400">
          Selected node: {selectedNodeData
            ? selectedNodeData.blockId !== null
              ? `${selectedNodeData.functionName} (block ${selectedNodeData.blockId})`
              : selectedNodeData.functionName
            : selectedNode}
        </p>
      ) : null}
    </div>
  );
}
