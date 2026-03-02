"use client";

import { useRef } from "react";
import { type Chart as ChartJS } from "chart.js";
import { Bar } from "react-chartjs-2";
import { ensureChartJsRegistered } from "./chartjs-setup";
import { downloadDataUrl } from "./utils";

ensureChartJsRegistered();

type HistogramRendererProps = {
  entries: Array<[string, number]>;
  label: string;
  filename: string;
};

export function HistogramRenderer({ entries, label, filename }: HistogramRendererProps) {
  const chartRef = useRef<ChartJS<"bar"> | null>(null);
  if (entries.length === 0) return <p className="text-sm text-zinc-400">No histogram data available.</p>;

  const values = entries.map(([, value]) => value);
  const useLog = values.some((value) => value > 300);

  return (
    <div className="space-y-3">
      <div className="flex gap-2">
        <button className="rounded bg-zinc-800 px-3 py-1 text-xs" onClick={() => chartRef.current?.resetZoom()}>
          Reset zoom
        </button>
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs"
          onClick={() => {
            const uri = chartRef.current?.toBase64Image();
            if (uri) downloadDataUrl(uri, filename);
          }}
        >
          Export PNG
        </button>
      </div>
      <Bar
        ref={chartRef}
        data={{
          labels: entries.map(([key]) => key),
          datasets: [
            {
              label,
              data: values,
              backgroundColor: "rgba(34,211,238,0.35)",
              borderColor: "rgba(34,211,238,1)",
              borderWidth: 1,
            },
          ],
        }}
        options={{
          responsive: true,
          interaction: { mode: "index", intersect: false },
          scales: {
            y: { type: useLog ? "logarithmic" : "linear" },
          },
          plugins: {
            zoom: {
              pan: { enabled: true, mode: "x" },
              zoom: { wheel: { enabled: true }, pinch: { enabled: true }, mode: "x" },
            },
          },
        }}
      />
    </div>
  );
}
