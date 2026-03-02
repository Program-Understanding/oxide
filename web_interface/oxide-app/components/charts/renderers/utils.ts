export type NormalizedGraph = {
  nodes: Array<{ id: string; functionName: string; blockId: number | null }>;
  edges: Array<{ id: string; source: string; target: string }>;
};

export function getModuleResult(result: unknown, oid: string): unknown {
  if (result && typeof result === "object" && !Array.isArray(result)) {
    const map = result as Record<string, unknown>;
    if (oid in map) {
      return map[oid];
    }
  }

  return result;
}

export function toEntries(obj: unknown): Array<[string, number]> {
  if (!obj || typeof obj !== "object" || Array.isArray(obj)) return [];
  return Object.entries(obj as Record<string, unknown>)
    .filter(([, value]) => typeof value === "number")
    .map(([key, value]) => [key, value as number]);
}

export function downloadDataUrl(dataUrl: string, filename: string) {
  const link = document.createElement("a");
  link.href = dataUrl;
  link.download = filename;
  link.click();
}

export function normalizeCallGraphData(data: any): NormalizedGraph {
  const nodeMap = new Map<string, { id: string; functionName: string; blockId: number | null }>();
  const edges: Array<{ id: string; source: string; target: string }> = [];

  const toNumericBlockId = (value: unknown): number | null => {
    if (typeof value === "number" && Number.isFinite(value)) return value;
    if (typeof value === "string" && /^\d+$/.test(value)) return Number(value);
    return null;
  };

  const addNode = (rawId: unknown, rawFunctionName?: unknown, rawBlockId?: unknown) => {
    if (rawId === undefined || rawId === null) return;
    const id = String(rawId);
    const functionName =
      rawFunctionName !== undefined && rawFunctionName !== null
        ? String(rawFunctionName)
        : id;
    const parsedBlockId = toNumericBlockId(rawBlockId);
    const inferredBlockId = parsedBlockId ?? toNumericBlockId(rawId);

    if (!nodeMap.has(id)) {
      nodeMap.set(id, { id, functionName, blockId: inferredBlockId });
      return;
    }

    const existing = nodeMap.get(id);
    if (existing && existing.blockId === null && inferredBlockId !== null) {
      nodeMap.set(id, { ...existing, blockId: inferredBlockId });
    }
  };

  const addEdge = (rawSource: unknown, rawTarget: unknown) => {
    if (
      rawSource === undefined ||
      rawSource === null ||
      rawTarget === undefined ||
      rawTarget === null
    ) {
      return;
    }

    const source = String(rawSource);
    const target = String(rawTarget);
    addNode(source);
    addNode(target);
    edges.push({ id: `e-${source}-${target}-${edges.length}`, source, target });
  };

  const rawNodes = Array.isArray(data?.nodes) ? data.nodes : [];
  const rawEdges = Array.isArray(data?.links)
    ? data.links
    : Array.isArray(data?.edges)
      ? data.edges
      : [];

  for (const node of rawNodes) {
    if (node && typeof node === "object") {
      addNode(
        node.id ?? node.name ?? node.label,
        node.function_name ?? node.label ?? node.name ?? node.id,
        node.block_id,
      );
    } else {
      addNode(node);
    }
  }

  for (const edge of rawEdges) {
    if (!edge || typeof edge !== "object") continue;
    addEdge(edge.source ?? edge.from, edge.target ?? edge.to);
  }

  if (nodeMap.size === 0 && data?.function_calls && typeof data.function_calls === "object") {
    for (const [caller, callInfo] of Object.entries(
      data.function_calls as Record<string, any>,
    )) {
      addNode(caller, caller);
      const calls = Array.isArray(callInfo?.calls) ? callInfo.calls : [];
      for (const callee of calls) {
        addEdge(caller, callee);
      }
    }
  }

  return {
    nodes: Array.from(nodeMap.values()),
    edges,
  };
}
