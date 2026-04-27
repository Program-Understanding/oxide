"use client";

import { useMemo } from "react";
import { useRef } from "react";
import { type Chart as ChartJS } from "chart.js";
import { Bar } from "react-chartjs-2";
import { ensureChartJsRegistered } from "./chartjs-setup";
import { downloadDataUrl } from "./utils";

ensureChartJsRegistered();

type CycloComplexityRendererProps = {
  data: unknown;
};

type FuncEntry = {
  name: string;
  complexity: number;
  desc: string;
};

const DESC_COLORS: Record<string, string> = {
  simple: "rgba(163,230,53,0.8)",
  moderate: "rgba(251,191,36,0.8)",
  complex: "rgba(251,146,60,0.8)",
  "needs refactor": "rgba(239,68,68,0.8)",
};

function normalizeDesc(desc: unknown): string {
  if (typeof desc !== "string") return "unknown";
  const d = desc.toLowerCase().trim();
  if (d === "simple") return "simple";
  if (d === "moderate") return "moderate";
  if (d === "complex") return "complex";
  if (d.includes("refactor")) return "needs refactor";
  return "unknown";
}

export function CycloComplexityRenderer({ data }: CycloComplexityRendererProps) {
  const chartRef = useRef<ChartJS<"bar"> | null>(null);

  const entries = useMemo<FuncEntry[]>(() => {
    if (Array.isArray(data)) {
      return (data as unknown[])
        .filter((item): item is Record<string, unknown> => item !== null && typeof item === "object")
        .map((item) => ({
          name: String(item.name ?? item.function ?? item.func ?? "unknown"),
          complexity: typeof item.complexity === "number" ? item.complexity : 0,
          desc: normalizeDesc(item.desc),
        }))
        .filter((item) => item.complexity > 0);
    }
    if (typeof data === "object" && data !== null) {
      const d = data as Record<string, unknown>;
      if (Array.isArray(d.functions)) {
        return (d.functions as unknown[])
          .filter((item): item is Record<string, unknown> => item !== null && typeof item === "object")
          .map((item) => ({
            name: String(item.name ?? item.function ?? item.func ?? "unknown"),
            complexity: typeof item.complexity === "number" ? item.complexity : 0,
            desc: normalizeDesc(item.desc),
          }))
          .filter((item) => item.complexity > 0);
      }
      // Handle OID-keyed objects: {"4096": {name, complexity, desc}, ...}
      return Object.values(d)
        .filter((v): v is Record<string, unknown> => v !== null && typeof v === "object")
        .map((item) => ({
          name: String(item.name ?? item.function ?? item.func ?? "unknown"),
          complexity: typeof item.complexity === "number" ? item.complexity : 0,
          desc: normalizeDesc(item.desc),
        }))
        .filter((item) => item.complexity > 0);
    }
    return [];
  }, [data]);

  if (entries.length === 0) {
    return <p className="text-sm text-zinc-400">No cyclomatic complexity data available.</p>;
  }

  const sorted = [...entries].sort((a, b) => b.complexity - a.complexity);
  const labels = sorted.map((e) => e.name);
  const values = sorted.map((e) => e.complexity);
  const colors = sorted.map((e) => DESC_COLORS[e.desc] ?? "rgba(156,163,175,0.8)");

  return (
    <div className="space-y-3">
      <div className="flex items-center justify-between">
        <p className="text-sm text-zinc-400">{entries.length} function{entries.length !== 1 ? "s" : ""}</p>
        <div className="flex gap-2">
          <button
            className="rounded bg-zinc-800 px-3 py-1 text-xs"
            onClick={() => chartRef.current?.resetZoom()}
          >
            Reset zoom
          </button>
          <button
            className="rounded bg-zinc-800 px-3 py-1 text-xs"
            onClick={() => {
              const uri = chartRef.current?.toBase64Image();
              if (uri) downloadDataUrl(uri, "cyclo_complexity.png");
            }}
          >
            Export PNG
          </button>
        </div>
      </div>
      <Bar
        ref={chartRef}
        data={{
          labels,
          datasets: [
            {
              label: "Cyclomatic Complexity",
              data: values,
              backgroundColor: colors,
              borderColor: colors.map((c) => c.replace("0.8", "1")),
              borderWidth: 1,
            },
          ],
        }}
        options={{
          indexAxis: "y" as const,
          responsive: true,
          scales: {
            x: { min: 0 },
          },
          plugins: {
            legend: { display: false },
            tooltip: {
              callbacks: {
                afterLabel(ctx) {
                  const entry = sorted[ctx.dataIndex];
                  return `Classification: ${entry.desc}`;
                },
              },
            },
            zoom: {
              pan: { enabled: true, mode: "y" },
              zoom: { wheel: { enabled: true }, pinch: { enabled: true }, mode: "y" },
            },
          },
        }}
      />
      <div className="flex flex-wrap gap-3 text-xs">
        {Object.entries(DESC_COLORS).map(([label, color]) => (
          <span key={label} className="flex items-center gap-1">
            <span className="inline-block h-3 w-3 rounded" style={{ backgroundColor: color }} />
            <span className="text-zinc-400">{label}</span>
          </span>
        ))}
      </div>
    </div>
  );
}