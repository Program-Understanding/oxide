"use client";

import { TriageRenderer } from "./renderers/triage-renderer";
import { CycloComplexityRenderer } from "./renderers/cyclo-complexity-renderer";
import { EntropyRenderer } from "./renderers/entropy-renderer";
import { HistogramRenderer } from "./renderers/histogram-renderer";
import { HeatmapRenderer } from "./renderers/heatmap-renderer";
import { CallGraphRenderer } from "./renderers/call-graph-renderer";
import { ControlFlowRenderer } from "./renderers/control-flow-renderer";
import { BinaryVisualizerRenderer } from "./renderers/binary-visualizer-renderer";
import type { ModuleRendererProps } from "./renderers/types";
import { getModuleResult, toEntries } from "./renderers/utils";
import { DepthJsonView } from "@/components/depth-json-view";

export function ChartRenderer({ moduleName, oid, result }: ModuleRendererProps) {
  const moduleData = getModuleResult(result, oid);

  if (!moduleData) {
    return <p className="text-sm text-zinc-400">No result available for selected module/file.</p>;
  }

  if (moduleName === "triage") return <TriageRenderer data={moduleData} />;
  if (moduleName === "cyclo_complexity") return <CycloComplexityRenderer data={moduleData} />;
  if (moduleName === "entropy_graph") return <EntropyRenderer data={moduleData} />;
  if (moduleName === "byte_histogram") {
    return (
      <HistogramRenderer
        entries={toEntries(moduleData)}
        label="Byte Frequency"
        filename="byte_histogram.png"
      />
    );
  }
  if (moduleName === "opcode_histogram") {
    return (
      <HistogramRenderer
        entries={toEntries(moduleData)}
        label="Opcode Frequency"
        filename="opcode_histogram.png"
      />
    );
  }
  if (moduleName === "byte_ngrams") {
    return (
      <HeatmapRenderer
        entries={toEntries(moduleData)}
        title="Byte N-grams"
        filename="byte_ngrams.png"
      />
    );
  }
  if (moduleName === "opcode_ngrams") {
    return (
      <HeatmapRenderer
        entries={toEntries(moduleData)}
        title="Opcode N-grams"
        filename="opcode_ngrams.png"
      />
    );
  }
  if (moduleName === "call_graph") return <CallGraphRenderer data={moduleData} />;
  if (moduleName === "control_flow_graph") return <ControlFlowRenderer data={moduleData} />;
  if (moduleName === "binary_visualizer") return <BinaryVisualizerRenderer data={moduleData} />;

  return <DepthJsonView data={moduleData} />;
}
