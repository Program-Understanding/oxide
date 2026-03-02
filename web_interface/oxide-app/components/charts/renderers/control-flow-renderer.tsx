"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { loadCytoscape } from "./cytoscape-loader";
import { downloadDataUrl } from "./utils";
import type { RendererDataProps } from "./types";

type CytoscapeCore = any;
type CytoscapeElementDefinition = any;

export function ControlFlowRenderer({ data }: RendererDataProps) {
  const containerRef = useRef<HTMLDivElement | null>(null);
  const cyRef = useRef<CytoscapeCore | null>(null);
  const [selectedFunction, setSelectedFunction] = useState<string>("");
  const [selectedBlockId, setSelectedBlockId] = useState<string>("");

  const functionNames = useMemo(
    () => Object.keys(data?.functions ?? {}).filter((name) => (data.functions?.[name]?.blocks ?? []).length > 0),
    [data],
  );

  const normalizeAddress = (value: string): string => {
    const trimmed = value.trim().toLowerCase();
    const withoutPrefix = trimmed.startsWith("0x") ? trimmed.slice(2) : trimmed;
    const normalized = withoutPrefix.replace(/^0+/, "");
    return normalized.length > 0 ? normalized : "0";
  };

  const functionLookup = useMemo(() => {
    const byExact = new Map<string, string>();
    const byAddress = new Map<string, string>();

    for (const name of functionNames) {
      const normalizedName = name.trim().toLowerCase();
      byExact.set(normalizedName, name);

      const addressMatch = normalizedName.match(/(?:0x)?([0-9a-f]{6,})$/);
      if (addressMatch?.[1]) {
        byAddress.set(normalizeAddress(addressMatch[1]), name);
      }
    }

    return { byExact, byAddress };
  }, [functionNames]);

  const instructionMap = useMemo(() => {
    const map = new Map<string, string[]>();
    const rawNodes = data?.nodes;

    if (Array.isArray(rawNodes)) {
      for (const node of rawNodes) {
        if (!node || typeof node !== "object") continue;
        const id = node["block id"] ?? node.block_id ?? node.id;
        if (id === undefined || id === null) continue;
        const instructions = Array.isArray(node.instructions)
          ? node.instructions.map((item: unknown) => String(item))
          : [];
        map.set(String(id), instructions);
      }
    } else if (rawNodes && typeof rawNodes === "object") {
      for (const [id, instructions] of Object.entries(rawNodes as Record<string, unknown>)) {
        const lines = Array.isArray(instructions)
          ? instructions.map((item: unknown) => String(item))
          : [String(instructions)];
        map.set(String(id), lines);
      }
    }

    return map;
  }, [data]);

  const blockIds: string[] = useMemo(
    () => (data?.functions?.[selectedFunction]?.blocks ?? []).map((blockId: unknown) => String(blockId)),
    [data, selectedFunction],
  );

  const blockIdSet = useMemo(() => new Set(blockIds), [blockIds]);

  const selectedInstructions = useMemo(
    () => instructionMap.get(selectedBlockId) ?? [],
    [instructionMap, selectedBlockId],
  );

  const resolveFunctionTarget = (token: string): string | null => {
    const cleanedToken = token.trim().replace(/[\],):>]*$/, "");
    if (!cleanedToken) return null;

    const exactMatch = functionLookup.byExact.get(cleanedToken.toLowerCase());
    if (exactMatch) return exactMatch;

    const addressMatch = cleanedToken.match(/(?:0x)?([0-9a-fA-F]{6,})$/);
    if (!addressMatch?.[1]) return null;

    return functionLookup.byAddress.get(normalizeAddress(addressMatch[1])) ?? null;
  };

  const renderInstructionLine = (line: string, index: number) => {
    const match = line.match(/^\s*([^,]+,)?\s*([a-z][a-z0-9]*)\s+(.+)$/i);
    if (!match) {
      return (
        <div key={`ins-${index}`} className="leading-5">
          {line}
        </div>
      );
    }

    const mnemonic = match[2].toLowerCase();
    const canJumpToTarget = mnemonic === "call" || mnemonic === "jmp" || mnemonic.startsWith("j") || mnemonic.startsWith("loop");
    if (!canJumpToTarget) {
      return (
        <div key={`ins-${index}`} className="leading-5">
          {line}
        </div>
      );
    }

    const targetToken = match[3].trim().split(/\s+/)[0]?.replace(/[;].*$/, "") ?? "";
    const targetFunction = resolveFunctionTarget(targetToken);

    if (!targetFunction) {
      return (
        <div key={`ins-${index}`} className="leading-5">
          {line}
        </div>
      );
    }

    const targetIndex = line.indexOf(targetToken);
    if (targetIndex < 0) {
      return (
        <div key={`ins-${index}`} className="leading-5">
          {line}
        </div>
      );
    }

    const prefix = line.slice(0, targetIndex);
    const suffix = line.slice(targetIndex + targetToken.length);

    return (
      <div key={`ins-${index}`} className="leading-5">
        <span>{prefix}</span>
        <button
          type="button"
          className="text-cyan-400 underline underline-offset-2 hover:text-cyan-300"
          onClick={() => setSelectedFunction(targetFunction)}
          title={`Jump to function ${targetFunction}`}
        >
          {targetToken}
        </button>
        <span>{suffix}</span>
      </div>
    );
  };

  const highlightSelectedBlock = (blockId: string) => {
    const cy = cyRef.current;
    if (!cy) return;

    cy.elements().removeClass("selected-node highlighted-in highlighted-out highlighted-edge-in highlighted-edge-out");
    const node = cy.$id(blockId);
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
    if (!selectedFunction && functionNames.length > 0) {
      setSelectedFunction(functionNames[0]);
    }
  }, [functionNames, selectedFunction]);

  useEffect(() => {
    if (blockIds.length === 0) {
      setSelectedBlockId("");
      return;
    }

    if (!selectedBlockId || !blockIdSet.has(selectedBlockId)) {
      setSelectedBlockId(blockIds[0]);
    }
  }, [blockIds, blockIdSet, selectedBlockId]);

  useEffect(() => {
    if (!containerRef.current || !selectedFunction) return;
    let cancelled = false;

    const nodes = blockIds.map((blockId: string) => {
      const firstInstruction = instructionMap.get(blockId)?.[0];
      const preview =
        firstInstruction && firstInstruction.length > 56
          ? `${firstInstruction.slice(0, 56)}…`
          : firstInstruction;

      return {
        data: {
          id: blockId,
          label: preview ? `Block ID: ${blockId}\n${preview}` : `Block ID: ${blockId}`,
        },
      };
    });
    const edges = (data?.edges ?? [])
      .map((edge: any, idx: number) => ({
        id: `e-${idx}`,
        source: String(edge?.from),
        target: String(edge?.to),
      }))
      .filter((edge: any) => blockIdSet.has(edge.source) && blockIdSet.has(edge.target))
      .map((edge: any) => ({ data: edge }));

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
              "background-color": "#0e7490",
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
        const blockId = event.target.id();
        setSelectedBlockId(blockId);
        highlightSelectedBlock(blockId);
      });

      cyRef.current.fit(undefined, 20);
    });

    return () => {
      cancelled = true;
      cyRef.current?.destroy();
      cyRef.current = null;
    };
  }, [data, selectedFunction, blockIds, blockIdSet, instructionMap]);

  useEffect(() => {
    if (!selectedBlockId) return;
    highlightSelectedBlock(selectedBlockId);
  }, [selectedBlockId]);

  if (functionNames.length === 0) return <p className="text-sm text-zinc-400">No control-flow data available.</p>;

  return (
    <div className="space-y-3">
      <div className="flex items-center gap-3">
        <label className="text-sm text-zinc-300">Function</label>
        <select className="rounded border border-zinc-800 bg-zinc-900 p-2 text-sm" value={selectedFunction} onChange={(e) => setSelectedFunction(e.target.value)}>
          {functionNames.map((name) => (
            <option key={name} value={name}>{name}</option>
          ))}
        </select>
        <button className="rounded bg-zinc-800 px-3 py-1 text-xs" onClick={() => cyRef.current?.fit()}>Fit graph</button>
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs"
          onClick={() => {
            const png = cyRef.current?.png({ bg: "#09090b", full: true, scale: 2 });
            if (png) downloadDataUrl(png, `cfg_${selectedFunction || "function"}.png`);
          }}
        >
          Export PNG
        </button>
      </div>
      <div ref={containerRef} className="h-[34rem] w-full rounded border border-zinc-800 bg-zinc-900" />
      <div className="rounded border border-zinc-800 p-3">
        <h3 className="mb-2 text-sm font-medium text-zinc-200">
          {selectedBlockId ? `Instructions for Block ${selectedBlockId}` : "Instructions"}
        </h3>
        <div className="max-h-48 overflow-auto whitespace-pre-wrap font-mono text-xs text-zinc-300">
          {selectedInstructions.length > 0
            ? selectedInstructions.map((line, index) => renderInstructionLine(line, index))
            : "No instructions available for selected block."}
        </div>
      </div>
    </div>
  );
}
