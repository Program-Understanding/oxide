"use client";

import { useEffect, useMemo, useState } from "react";
import dynamic from "next/dynamic";
import { apiClient } from "@/lib/api/client";
import type { CollectionFile, ModuleCapability } from "@/lib/api/types";

const ChartRenderer = dynamic(
  () => import("@/components/charts/chart-renderers").then((mod) => mod.ChartRenderer),
  { ssr: false },
);

type RunState = {
  loading: boolean;
  error: string | null;
  result: unknown;
  resultModule: string | null;
  resultOid: string | null;
};

type ChartsWorkspaceProps = {
  capabilities: ModuleCapability[];
};

function chartLabel(moduleName: string): string {
  const labels: Record<string, string> = {
    entropy_graph: "Entropy Graph",
    byte_histogram: "Byte Histogram",
    byte_ngrams: "Byte N-grams",
    opcode_histogram: "Opcode Histogram",
    opcode_ngrams: "Opcode N-grams",
    call_graph: "Call Graph",
    control_flow_graph: "Control Flow Graph",
    binary_visualizer: "Binary Visualizer",
  };
  return labels[moduleName] ?? moduleName;
}

export function ChartsWorkspace({ capabilities }: ChartsWorkspaceProps) {
  const [collections, setCollections] = useState<string[]>([]);
  const [files, setFiles] = useState<CollectionFile[]>([]);

  const [selectedCollection, setSelectedCollection] = useState<string>("");
  const [selectedOid, setSelectedOid] = useState<string>("");
  const [selectedChartModule, setSelectedChartModule] = useState<string>("");

  const [runState, setRunState] = useState<RunState>({
    loading: false,
    error: null,
    result: null,
    resultModule: null,
    resultOid: null,
  });

  const availableModules = useMemo(
    () => capabilities.filter((capability) => capability.available).map((capability) => capability.module),
    [capabilities],
  );

  useEffect(() => {
    let mounted = true;
    apiClient
      .getCollections()
      .then((response) => {
        if (!mounted) return;
        setCollections(response.collections);
      })
      .catch((err: unknown) => {
        if (!mounted) return;
        setRunState({
          loading: false,
          error: err instanceof Error ? err.message : "Failed to load collections",
          result: null,
          resultModule: null,
          resultOid: null,
        });
      });

    return () => {
      mounted = false;
    };
  }, []);

  useEffect(() => {
    if (!selectedCollection) {
      setFiles([]);
      setSelectedOid("");
      return;
    }

    let mounted = true;
    apiClient
      .getCollectionFiles(selectedCollection)
      .then((response) => {
        if (!mounted) return;
        setFiles(response.files);
        setSelectedOid("");
      })
      .catch((err: unknown) => {
        if (!mounted) return;
        setRunState({
          loading: false,
          error: err instanceof Error ? err.message : "Failed to load collection files",
          result: null,
          resultModule: null,
          resultOid: null,
        });
      });

    return () => {
      mounted = false;
    };
  }, [selectedCollection]);

  useEffect(() => {
    setRunState((previous) => {
      if (
        previous.result === null &&
        previous.error === null &&
        previous.resultModule === null &&
        previous.resultOid === null
      ) {
        return previous;
      }

      return {
        ...previous,
        error: null,
        result: null,
        resultModule: null,
        resultOid: null,
      };
    });
  }, [selectedChartModule, selectedOid]);

  const selectedFile = useMemo(
    () => files.find((file) => file.oid === selectedOid) ?? null,
    [files, selectedOid],
  );

  async function runChartModule() {
    if (!selectedChartModule || !selectedOid) {
      return;
    }

    setRunState({
      loading: true,
      error: null,
      result: null,
      resultModule: null,
      resultOid: null,
    });
    try {
      const response = await apiClient.retrieve({
        module: selectedChartModule,
        oid: selectedOid,
        opts: {},
      });
      setRunState({
        loading: false,
        error: null,
        result: response.results,
        resultModule: selectedChartModule,
        resultOid: selectedOid,
      });
    } catch (err: unknown) {
      setRunState({
        loading: false,
        error: err instanceof Error ? err.message : "Chart module execution failed",
        result: null,
        resultModule: null,
        resultOid: null,
      });
    }
  }

  const hasFreshResult =
    runState.result !== null &&
    runState.resultModule === selectedChartModule &&
    runState.resultOid === selectedOid;

  return (
    <section className="space-y-4">
      <div className="rounded border border-zinc-800 p-4">
        <h2 className="mb-2 font-medium">Chart Module Availability</h2>
        <ul className="space-y-1 text-sm text-zinc-300">
          {capabilities.map((capability) => (
            <li key={capability.module} className="flex items-center justify-between">
              <span>{chartLabel(capability.module)}</span>
              <span
                className={
                  capability.available
                    ? "rounded bg-emerald-900/40 px-2 py-0.5 text-emerald-300"
                    : "rounded bg-red-900/40 px-2 py-0.5 text-red-300"
                }
              >
                {capability.available ? "available" : "missing"}
              </span>
            </li>
          ))}
        </ul>
      </div>

      <div className="grid grid-cols-1 gap-4 md:grid-cols-3">
        <label className="flex flex-col gap-2 text-sm">
          <span className="text-zinc-300">Collection</span>
          <select
            className="rounded border border-zinc-800 bg-zinc-900 p-2"
            value={selectedCollection}
            onChange={(event) => setSelectedCollection(event.target.value)}
          >
            <option value="">Select collection</option>
            {collections.map((collection) => (
              <option key={collection} value={collection}>
                {collection}
              </option>
            ))}
          </select>
        </label>

        <label className="flex flex-col gap-2 text-sm">
          <span className="text-zinc-300">File (OID)</span>
          <select
            className="rounded border border-zinc-800 bg-zinc-900 p-2"
            value={selectedOid}
            onChange={(event) => setSelectedOid(event.target.value)}
            disabled={!selectedCollection}
          >
            <option value="">Select file</option>
            {files.map((file) => (
              <option key={file.oid} value={file.oid}>
                {file.names[0] ?? file.oid}
              </option>
            ))}
          </select>
        </label>

        <label className="flex flex-col gap-2 text-sm">
          <span className="text-zinc-300">Chart Module</span>
          <select
            className="rounded border border-zinc-800 bg-zinc-900 p-2"
            value={selectedChartModule}
            onChange={(event) => setSelectedChartModule(event.target.value)}
          >
            <option value="">Select chart module</option>
            {availableModules.map((moduleName) => (
              <option key={moduleName} value={moduleName}>
                {chartLabel(moduleName)}
              </option>
            ))}
          </select>
        </label>
      </div>

      <div className="flex items-center gap-3">
        <button
          className="rounded bg-sky-600 px-4 py-2 text-sm font-medium text-white disabled:cursor-not-allowed disabled:bg-zinc-700"
          disabled={!selectedChartModule || !selectedOid || runState.loading}
          onClick={runChartModule}
        >
          {runState.loading ? "Running..." : "Run chart module"}
        </button>
        {selectedFile && (
          <p className="text-xs text-zinc-400">
            Selected: {selectedFile.names.join(", ")} ({selectedFile.oid})
          </p>
        )}
      </div>

      {runState.error && (
        <div className="rounded border border-red-700 bg-red-950/40 p-3 text-sm text-red-200">
          {runState.error}
        </div>
      )}

      <div className="rounded border border-zinc-800 p-4">
        <h2 className="mb-2 font-medium">Chart Module Result</h2>
        {selectedChartModule && selectedOid && hasFreshResult ? (
          <div className="mb-4">
            <ChartRenderer moduleName={selectedChartModule} oid={selectedOid} result={runState.result} />
          </div>
        ) : null}
        <pre className="max-h-[34rem] overflow-auto text-xs text-zinc-300">
          {JSON.stringify(runState.result, null, 2)}
        </pre>
      </div>
    </section>
  );
}
