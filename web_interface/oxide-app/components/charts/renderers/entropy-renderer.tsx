"use client";

import { useRef } from "react";
import { type Chart as ChartJS } from "chart.js";
import { Line } from "react-chartjs-2";
import { ensureChartJsRegistered } from "./chartjs-setup";
import { downloadDataUrl } from "./utils";
import type { RendererDataProps } from "./types";

ensureChartJsRegistered();

export function EntropyRenderer({ data }: RendererDataProps) {
  const chartRef = useRef<ChartJS<"line"> | null>(null);

  if (!data?.entropies || !data?.addresses) {
    return <p className="text-sm text-zinc-400">No entropy data available.</p>;
  }

  const labels = data.addresses.map((address: number) =>
    `0x${address.toString(16).toUpperCase()}`,
  );
  const chartData = {
    labels,
    datasets: [
      {
        label: "Entropy",
        data: data.entropies,
        borderColor: "rgb(34,211,238)",
        backgroundColor: "rgba(34,211,238,0.3)",
        pointRadius: 0,
        tension: 0.1,
      },
    ],
  };

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
            if (uri) downloadDataUrl(uri, "entropy_graph.png");
          }}
        >
          Export PNG
        </button>
      </div>
      <Line
        ref={chartRef}
        data={chartData}
        options={{
          responsive: true,
          interaction: { mode: "nearest", intersect: false },
          scales: { y: { min: 0, max: 1 } },
          plugins: {
            zoom: {
              pan: { enabled: true, mode: "x" },
              zoom: { wheel: { enabled: true }, pinch: { enabled: true }, mode: "x" },
            },
          },
        }}
      />
      <div className="grid grid-cols-2 gap-2 text-xs md:grid-cols-4">
        <div className="rounded border border-zinc-800 p-2">Block size: {String(data.block_size)}</div>
        <div className="rounded border border-zinc-800 p-2">Overall entropy: {String(data.overall_entropy)}</div>
        <div className="rounded border border-zinc-800 p-2">Max entropy: {String(data.max_entropy)}</div>
        <div className="rounded border border-zinc-800 p-2">Max entropy address: {String(data.max_entropy_address)}</div>
      </div>
    </div>
  );
}
