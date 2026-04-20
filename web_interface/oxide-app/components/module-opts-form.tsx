"use client";

import { useState } from "react";
import type { OptEntry } from "@/lib/api/types";

type ModuleOptsFormProps = {
  optsDoc: Record<string, OptEntry>;
  onChange: (opts: Record<string, unknown>) => void;
};

export function ModuleOptsForm({ optsDoc, onChange }: ModuleOptsFormProps) {
  const entries = Object.entries(optsDoc);
  if (entries.length === 0) return null;

  // Initialize state from defaults
  const [values, setValues] = useState<Record<string, unknown>>(() => {
    const init: Record<string, unknown> = {};
    for (const [key, opt] of entries) {
      if (opt.type === "bool") {
        init[key] = opt.default === true;
      } else if (opt.type === "int") {
        init[key] =
          opt.default !== null && opt.default !== undefined
            ? Number(opt.default)
            : "";
      } else {
        init[key] = opt.default ?? "";
      }
    }
    return init;
  });

  function handleChange(key: string, opt: OptEntry, raw: string | boolean) {
    let value: unknown;
    if (opt.type === "bool") {
      value = raw;
    } else if (opt.type === "int") {
      value = raw === "" ? null : parseInt(raw as string, 10);
    } else {
      value = raw;
    }
    const next = { ...values, [key]: value };
    setValues(next);
    onChange(next);
  }

  return (
    <div className="rounded border border-zinc-800 p-3">
      <p className="mb-2 text-xs font-medium uppercase tracking-wider text-zinc-500">
        Options
      </p>
      <div className="flex flex-wrap gap-4">
        {entries.map(([key, opt]) => (
          <label key={key} className="flex flex-col gap-1 text-sm">
            <span className="text-zinc-400">
              {key}
              {opt.mangle && (
                <span
                  className="ml-1 text-xs text-zinc-600"
                  title="Affects caching key"
                >
                  (cache key)
                </span>
              )}
            </span>
            {opt.type === "bool" ? (
              <input
                type="checkbox"
                className="rounded border-zinc-700 bg-zinc-900"
                checked={Boolean(values[key])}
                onChange={(e) => handleChange(key, opt, e.target.checked)}
              />
            ) : opt.type === "int" ? (
              <input
                type="number"
                className="rounded border border-zinc-700 bg-zinc-900 px-2 py-1"
                value={values[key] ?? ""}
                onChange={(e) => handleChange(key, opt, e.target.value)}
              />
            ) : (
              <input
                type="text"
                className="rounded border border-zinc-700 bg-zinc-900 px-2 py-1"
                value={values[key] ?? ""}
                onChange={(e) => handleChange(key, opt, e.target.value)}
              />
            )}
          </label>
        ))}
      </div>
    </div>
  );
}