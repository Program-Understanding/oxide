"use client";

import { useRef } from "react";
import { type Chart } from "chart.js";
import { Chart as ReactChart } from "react-chartjs-2";
import { ensureChartJsRegistered } from "./chartjs-setup";
import { downloadDataUrl } from "./utils";

ensureChartJsRegistered();

type HeatmapRendererProps = {
  entries: Array<[string, number]>;
  title: string;
  filename: string;
};

export function HeatmapRenderer({ entries, title, filename }: HeatmapRendererProps) {
  const chartRef = useRef<Chart<"matrix"> | null>(null);
  if (entries.length === 0) return <p className="text-sm text-zinc-400">No n-gram data available.</p>;

  const total = entries.length;
  const cols = Math.ceil(Math.sqrt(total));
  const rows = Math.ceil(total / cols);
  const maxValue = Math.max(...entries.map(([, v]) => v), 1);
  const data = entries.map(([, value], index) => ({ x: index % cols, y: Math.floor(index / cols), v: value }));

  return (
    <div className="space-y-3">
      <div className="flex gap-2">
        <button className="rounded bg-zinc-800 px-3 py-1 text-xs" onClick={() => chartRef.current?.resetZoom?.()}>
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
      <ReactChart
        ref={chartRef}
        type="matrix"
        data={{
          datasets: [
            {
              label: title,
              data,
              borderWidth: 0.5,
              borderColor: "rgba(255,255,255,0.1)",
              backgroundColor(context: any) {
                const value = context.dataset.data[context.dataIndex].v;
                const ratio = Math.log(value + 1) / Math.log(maxValue + 1);
                const r = Math.floor(255 * ratio);
                const g = Math.floor(255 * (1 - ratio));
                return `rgba(${r},${g},30,1)`;
              },
              width(context: any) {
                const area = context.chart.chartArea;
                return area ? area.width / cols : 8;
              },
              height(context: any) {
                const area = context.chart.chartArea;
                return area ? area.height / rows : 8;
              },
            },
          ],
        }}
        options={{
          scales: {
            x: { ticks: { display: false } },
            y: { ticks: { display: false } },
          },
          plugins: {
            legend: { display: false },
            tooltip: {
              callbacks: {
                label(context: any) {
                  const i = context.dataIndex;
                  const [label, value] = entries[i];
                  return `${label}: ${value}`;
                },
              },
            },
            zoom: {
              pan: { enabled: true, mode: "xy" },
              zoom: { wheel: { enabled: true }, pinch: { enabled: true }, mode: "xy" },
            },
          },
        }}
      />
    </div>
  );
}
