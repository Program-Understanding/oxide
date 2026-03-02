"use client";

import type { ReactNode } from "react";

type DepthJsonViewProps = {
  data: unknown;
  className?: string;
};

const DEPTH_KEY_CLASSES = [
  "text-sky-300",
  "text-emerald-300",
  "text-violet-300",
  "text-amber-300",
  "text-rose-300",
  "text-cyan-300",
];

const STRING_VALUE_CLASS = "text-orange-200";
const NUMBER_VALUE_CLASS = "text-fuchsia-300";
const BOOLEAN_VALUE_CLASS = "text-orange-300";
const NULL_VALUE_CLASS = "text-zinc-500";

function indent(level: number): string {
  return "  ".repeat(level);
}

function keyDepthClass(depth: number): string {
  return DEPTH_KEY_CLASSES[depth % DEPTH_KEY_CLASSES.length];
}

function renderPrimitive(value: unknown): ReactNode {
  if (typeof value === "string") {
    return <span className={STRING_VALUE_CLASS}>{JSON.stringify(value)}</span>;
  }

  if (typeof value === "number") {
    if (Number.isFinite(value)) {
      return <span className={NUMBER_VALUE_CLASS}>{String(value)}</span>;
    }

    return <span className={NULL_VALUE_CLASS}>null</span>;
  }

  if (typeof value === "boolean") {
    return <span className={BOOLEAN_VALUE_CLASS}>{String(value)}</span>;
  }

  if (value === null) {
    return <span className={NULL_VALUE_CLASS}>null</span>;
  }

  return <span className={STRING_VALUE_CLASS}>{JSON.stringify(String(value))}</span>;
}

function renderJson(value: unknown, depth: number): ReactNode {
  if (Array.isArray(value)) {
    if (value.length === 0) return "[]";

    return (
      <>
        [
        {"\n"}
        {value.map((item, index) => (
          <span key={`arr-${depth}-${index}`}>
            {indent(depth + 1)}
            {renderJson(item, depth + 1)}
            {index < value.length - 1 ? "," : ""}
            {"\n"}
          </span>
        ))}
        {indent(depth)}]
      </>
    );
  }

  if (value && typeof value === "object") {
    const entries = Object.entries(value as Record<string, unknown>);
    if (entries.length === 0) return "{}";

    return (
      <>
        {"{"}
        {"\n"}
        {entries.map(([key, nested], index) => (
          <span key={`obj-${depth}-${key}-${index}`}>
            {indent(depth + 1)}
            <span className={keyDepthClass(depth)}>{JSON.stringify(key)}</span>
            {": "}
            {renderJson(nested, depth + 1)}
            {index < entries.length - 1 ? "," : ""}
            {"\n"}
          </span>
        ))}
        {indent(depth)}
        {"}"}
      </>
    );
  }

  return renderPrimitive(value);
}

export function DepthJsonView({ data, className }: DepthJsonViewProps) {
  return (
    <pre className={`max-h-[34rem] overflow-auto whitespace-pre text-xs text-zinc-300 ${className ?? ""}`}>
      {renderJson(data, 0)}
    </pre>
  );
}
