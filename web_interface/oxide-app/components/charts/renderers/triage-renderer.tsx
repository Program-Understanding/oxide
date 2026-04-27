"use client";

import { useMemo, useRef } from "react";
import { type Chart as ChartJS } from "chart.js";
import { Doughnut } from "react-chartjs-2";
import { ensureChartJsRegistered } from "./chartjs-setup";
import { downloadDataUrl } from "./utils";

ensureChartJsRegistered();

type TriageRendererProps = {
  data: unknown;
};

const CATEGORY_COLORS: Record<string, string> = {
  executable: "rgba(34,211,238,0.8)",
  archive: "rgba(251,146,60,0.8)",
  media: "rgba(163,230,53,0.8)",
  documentation: "rgba(167,139,250,0.8)",
  resource: "rgba(251,191,36,0.8)",
  source: "rgba(96,165,250,0.8)",
};

const CATEGORIES = ["executable", "archive", "media", "documentation", "resource", "source"];

export function TriageRenderer({ data }: TriageRendererProps) {
  const chartRef = useRef<ChartJS<"doughnut"> | null>(null);

  const parsed = useMemo(() => {
    if (typeof data !== "object" || data === null) return null;
    const d = data as Record<string, unknown>;
    return CATEGORIES.map((cat) => {
      const val = d[cat];
      if (typeof val === "object" && val !== null && "total" in val) {
        return { cat, count: typeof (val as Record<string, unknown>).total === "number" ? (val as Record<string, unknown>).total as number : 0 };
      }
      if (typeof val === "number") {
        return { cat, count: val };
      }
      return { cat, count: 0 };
    });
  }, [data]);

  if (!parsed) {
    return <p className="text-sm text-zinc-400">No triage data available.</p>;
  }

  const total = parsed.reduce((s, { count }) => s + count, 0);

  return (
    <div className="space-y-2">
      <div className="flex items-center justify-between">
        <p className="text-sm text-zinc-400">Total: {total} file{total !== 1 ? "s" : ""}</p>
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs"
          onClick={() => {
            const uri = chartRef.current?.toBase64Image();
            if (uri) downloadDataUrl(uri, "triage.png");
          }}
        >
          Export PNG
        </button>
      </div>
      <div className="mx-auto max-w-sm">
        <Doughnut
          ref={chartRef}
          data={{
            labels: parsed.map(({ cat }) => cat),
            datasets: [
              {
                data: parsed.map(({ count }) => count),
                backgroundColor: parsed.map(({ cat }) => CATEGORY_COLORS[cat] ?? "rgba(156,163,175,0.8)"),
                borderColor: parsed.map(({ cat }) => (CATEGORY_COLORS[cat] ?? "rgba(156,163,175,0.8)").replace("0.8", "1")),
                borderWidth: 1,
              },
            ],
          }}
          options={{
            responsive: true,
            maintainAspectRatio: true,
            plugins: {
              legend: { position: "bottom" },
            },
          }}
        />
      </div>
      <div className="grid grid-cols-2 gap-1 text-xs text-zinc-400">
        {parsed.map(({ cat, count }) => (
          <span key={cat}>
            {cat}: {count}
          </span>
        ))}
      </div>
    </div>
  );
}
