"use client";

import { useEffect, useMemo, useRef, useState } from "react";
import { downloadDataUrl } from "./utils";
import type { RendererDataProps } from "./types";

export function BinaryVisualizerRenderer({ data }: RendererDataProps) {
  const canvasRef = useRef<HTMLCanvasElement | null>(null);
  const [cellSize, setCellSize] = useState(4);
  const [hoverInfo, setHoverInfo] = useState<string>("");

  const grid: number[][] = useMemo(() => {
    if (typeof data !== "string") return [];
    try {
      const parsed = JSON.parse(data);
      return Array.isArray(parsed) ? (parsed as number[][]) : [];
    } catch {
      return [];
    }
  }, [data]);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas || grid.length === 0) return;
    const cols = grid[0]?.length ?? 0;
    if (!cols) return;

    canvas.width = cols * cellSize;
    canvas.height = grid.length * cellSize;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;

    const color = (value: number) => {
      const t = Math.max(0, Math.min(1, value / 255));
      const r = Math.floor(68 + 160 * t);
      const g = Math.floor(1 + 220 * (1 - t));
      const b = Math.floor(84 + 80 * t);
      return `rgb(${r},${g},${b})`;
    };

    for (let y = 0; y < grid.length; y += 1) {
      for (let x = 0; x < cols; x += 1) {
        const value = grid[y][x] ?? 0;
        ctx.fillStyle = color(value);
        ctx.fillRect(x * cellSize, y * cellSize, cellSize, cellSize);
      }
    }

    const onMove = (event: MouseEvent) => {
      const rect = canvas.getBoundingClientRect();
      const x = Math.floor((event.clientX - rect.left) / cellSize);
      const y = Math.floor((event.clientY - rect.top) / cellSize);
      const value = grid[y]?.[x];
      if (typeof value === "number") {
        setHoverInfo(
          `row=${y}, col=${x}, dec=${value}, hex=0x${value.toString(16).toUpperCase().padStart(2, "0")}`,
        );
      }
    };

    canvas.addEventListener("mousemove", onMove);
    return () => canvas.removeEventListener("mousemove", onMove);
  }, [grid, cellSize]);

  if (grid.length === 0) return <p className="text-sm text-zinc-400">No binary visualizer data available.</p>;

  return (
    <div className="space-y-3">
      <div className="flex items-center gap-3">
        <label className="text-sm text-zinc-300">Zoom</label>
        <input
          type="range"
          min={2}
          max={16}
          value={cellSize}
          onChange={(e) => setCellSize(Number(e.target.value))}
        />
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs"
          onClick={() => {
            const uri = canvasRef.current?.toDataURL("image/png");
            if (uri) downloadDataUrl(uri, "binary_visualizer.png");
          }}
        >
          Export PNG
        </button>
      </div>
      <div className="max-h-[34rem] overflow-auto rounded border border-zinc-800 bg-zinc-900 p-1">
        <canvas ref={canvasRef} />
      </div>
      <p className="text-xs text-zinc-400">{hoverInfo}</p>
    </div>
  );
}
