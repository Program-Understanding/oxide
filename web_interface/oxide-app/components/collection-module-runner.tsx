"use client";

import { useEffect, useMemo, useState } from "react";
import { apiClient } from "@/lib/api/client";
import type { OptEntry } from "@/lib/api/types";
import { DepthJsonView } from "@/components/depth-json-view";
import { ModuleOptsForm } from "@/components/module-opts-form";

type RunState = {
  loading: boolean;
  error: string | null;
  result: unknown;
  resultModule: string | null;
  resultCollection: string | null;
};

export function CollectionModuleRunner() {
  const [collections, setCollections] = useState<string[]>([]);
  const [modules, setModules] = useState<string[]>([]);
  const [fileCount, setFileCount] = useState<number>(0);

  const [selectedCollection, setSelectedCollection] = useState<string>("");
  const [selectedModule, setSelectedModule] = useState<string>("");
  const [moduleSearch, setModuleSearch] = useState<string>("");
  const [moduleDropdownOpen, setModuleDropdownOpen] = useState(false);
  const [optsDoc, setOptsDoc] = useState<Record<string, OptEntry>>({});
  const [currentOpts, setCurrentOpts] = useState<Record<string, unknown>>({});

  const [runState, setRunState] = useState<RunState>({
    loading: false,
    error: null,
    result: null,
    resultModule: null,
    resultCollection: null,
  });

  useEffect(() => {
    let mounted = true;
    Promise.all([apiClient.getCollections(), apiClient.getModules()])
      .then(([collectionResp, modulesResp]) => {
        if (!mounted) return;
        setCollections(collectionResp.collections);
        setModules(modulesResp.modules);
      })
      .catch((err: unknown) => {
        if (!mounted) return;
        setRunState({
          loading: false,
          error: err instanceof Error ? err.message : "Failed to load initial data",
          result: null,
          resultModule: null,
          resultCollection: null,
        });
      });

    return () => {
      mounted = false;
    };
  }, []);

  useEffect(() => {
    if (!selectedCollection) {
      setFileCount(0);
      return;
    }

    let mounted = true;
    apiClient
      .getCollectionFiles(selectedCollection)
      .then((resp) => {
        if (!mounted) return;
        setFileCount(resp.files.length);
      })
      .catch(() => {
        if (!mounted) return;
        setFileCount(0);
      });

    return () => {
      mounted = false;
    };
  }, [selectedCollection]);

  useEffect(() => {
    if (!selectedModule) {
      setOptsDoc({});
      setCurrentOpts({});
      return;
    }

    let mounted = true;
    apiClient
      .getModuleDocumentation(selectedModule)
      .then((doc) => {
        if (!mounted) return;
        setOptsDoc(doc.opts_doc);
        const init: Record<string, unknown> = {};
        for (const [key, opt] of Object.entries(doc.opts_doc)) {
          if (opt.default !== null && opt.default !== undefined) {
            init[key] = opt.default;
          }
        }
        setCurrentOpts(init);
      })
      .catch(() => {
        if (!mounted) return;
        setOptsDoc({});
        setCurrentOpts({});
      });

    return () => {
      mounted = false;
    };
  }, [selectedModule]);

  useEffect(() => {
    setRunState((prev) => ({
      loading: false,
      error: null,
      result: null,
      resultModule: null,
      resultCollection: null,
    }));
  }, [selectedModule, selectedCollection]);

  const filteredModules = useMemo(() => {
    if (!moduleSearch.trim()) return modules;
    return modules.filter((m) => m.toLowerCase().includes(moduleSearch.toLowerCase()));
  }, [modules, moduleSearch]);

  async function runModule() {
    if (!selectedModule || !selectedCollection) return;

    setRunState({
      loading: true,
      error: null,
      result: null,
      resultModule: null,
      resultCollection: null,
    });
    try {
      const response = await apiClient.retrieve({
        module: selectedModule,
        collection: selectedCollection,
        opts: currentOpts,
      });
      setRunState({
        loading: false,
        error: null,
        result: response,
        resultModule: selectedModule,
        resultCollection: selectedCollection,
      });
    } catch (err: unknown) {
      setRunState({
        loading: false,
        error: err instanceof Error ? err.message : "Module execution failed",
        result: null,
        resultModule: null,
        resultCollection: null,
      });
    }
  }

  const hasFreshResult =
    runState.result !== null &&
    runState.resultModule === selectedModule &&
    runState.resultCollection === selectedCollection;

  return (
    <section className="space-y-4">
      <div className="grid grid-cols-1 gap-4 md:grid-cols-3">
        <label className="flex flex-col gap-2 text-sm">
          <span className="text-zinc-300">Collection</span>
          <select
            className="rounded border border-zinc-800 bg-zinc-900 p-2"
            value={selectedCollection}
            onChange={(e) => setSelectedCollection(e.target.value)}
          >
            <option value="">Select collection</option>
            {collections.map((col) => (
              <option key={col} value={col}>
                {col}
              </option>
            ))}
          </select>
          {selectedCollection && (
            <span className="text-xs text-zinc-500">{fileCount} file{fileCount !== 1 ? "s" : ""}</span>
          )}
        </label>

        <label className="flex flex-col gap-2 text-sm">
          <span className="text-zinc-300">Module</span>
          <div className="relative">
            <input
              type="text"
              className="w-full rounded border border-zinc-800 bg-zinc-900 p-2 text-sm"
              placeholder={selectedModule || "Search or click..."}
              value={moduleSearch}
              onChange={(e) => {
                setModuleSearch(e.target.value);
                setModuleDropdownOpen(true);
              }}
              onFocus={() => setModuleDropdownOpen(true)}
              onBlur={() => setTimeout(() => setModuleDropdownOpen(false), 150)}
            />
            {(moduleSearch || moduleDropdownOpen) && (
              <div className="absolute z-10 mt-1 max-h-48 w-full overflow-y-auto rounded border border-zinc-700 bg-zinc-900">
                {filteredModules.length === 0 ? (
                  <p className="p-2 text-xs text-zinc-500">No modules found</p>
                ) : (
                  filteredModules.map((mod) => (
                    <button
                      key={mod}
                      className="w-full px-3 py-1.5 text-left text-sm text-zinc-300 hover:bg-zinc-800"
                      onClick={() => {
                        setSelectedModule(mod);
                        setModuleSearch("");
                        setModuleDropdownOpen(false);
                      }}
                    >
                      {mod}
                    </button>
                  ))
                )}
              </div>
            )}
          </div>
        </label>

        <div className="flex items-end">
          <button
            className="rounded bg-sky-600 px-4 py-2 text-sm font-medium text-white disabled:cursor-not-allowed disabled:bg-zinc-700"
            disabled={!selectedModule || !selectedCollection || runState.loading}
            onClick={runModule}
          >
            {runState.loading ? "Running..." : "Run on collection"}
          </button>
        </div>
      </div>

      <ModuleOptsForm optsDoc={optsDoc} onChange={setCurrentOpts} />

      {runState.error && (
        <div className="rounded border border-red-700 bg-red-950/40 p-3 text-sm text-red-200">
          {runState.error}
        </div>
      )}

      <div className="rounded border border-zinc-800 p-4">
        <h2 className="mb-2 font-medium">Result</h2>
        <DepthJsonView data={hasFreshResult ? runState.result : null} />
      </div>
    </section>
  );
}