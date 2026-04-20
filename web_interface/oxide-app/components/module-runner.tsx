"use client";

import { useEffect, useMemo, useState } from "react";
import { apiClient } from "@/lib/api/client";
import type { CollectionFile, OptEntry, UploadResponse } from "@/lib/api/types";
import { DepthJsonView } from "@/components/depth-json-view";
import { ModuleOptsForm } from "@/components/module-opts-form";
import { FileDropzone } from "@/components/file-dropzone";

type RunState = {
  loading: boolean;
  error: string | null;
  result: unknown;
  resultModule: string | null;
  resultOid: string | null;
};

export function ModuleRunner() {
  const [collections, setCollections] = useState<string[]>([]);
  const [modules, setModules] = useState<string[]>([]);
  const [files, setFiles] = useState<CollectionFile[]>([]);

  const [selectedCollection, setSelectedCollection] = useState<string>("");
  const [selectedOid, setSelectedOid] = useState<string>("");
  const [selectedModule, setSelectedModule] = useState<string>("");
  const [optsDoc, setOptsDoc] = useState<Record<string, OptEntry>>({});
  const [currentOpts, setCurrentOpts] = useState<Record<string, unknown>>({});

  const [runState, setRunState] = useState<RunState>({
    loading: false,
    error: null,
    result: null,
    resultModule: null,
    resultOid: null,
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
      .then((resp) => {
        if (!mounted) return;
        setFiles(resp.files);
        setSelectedOid("");
      })
      .catch((err: unknown) => {
        if (!mounted) return;
        setFiles([]);
        setSelectedOid("");
        setRunState({
          loading: false,
          error: err instanceof Error ? err.message : "Failed to load files",
          result: null,
          resultModule: null,
          resultOid: null,
        });
      });

    return () => {
      mounted = false;
    };
  }, [selectedCollection]);

  // Fetch module options documentation when module selection changes
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
        // Build initial opts from defaults
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
  }, [selectedModule, selectedOid]);

  const selectedFile = useMemo(
    () => files.find((file) => file.oid === selectedOid) ?? null,
    [files, selectedOid],
  );

  async function runModule() {
    if (!selectedModule || !selectedOid) {
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
        module: selectedModule,
        oid: selectedOid,
        opts: currentOpts,
      });
      setRunState({
        loading: false,
        error: null,
        result: response,
        resultModule: selectedModule,
        resultOid: selectedOid,
      });
    } catch (err: unknown) {
      setRunState({
        loading: false,
        error: err instanceof Error ? err.message : "Module execution failed",
        result: null,
        resultModule: null,
        resultOid: null,
      });
    }
  }

  const hasFreshResult =
    runState.result !== null &&
    runState.resultModule === selectedModule &&
    runState.resultOid === selectedOid;

  function handleUploadComplete(_results: UploadResponse, newCollectionName: string) {
    void apiClient.getCollections().then((resp) => {
      setCollections(resp.collections);
      if (newCollectionName) {
        setSelectedCollection(newCollectionName);
      }
    });
  }

  return (
    <section className="space-y-4">
      <FileDropzone onUploadComplete={handleUploadComplete} />

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
          <span className="text-zinc-300">Module</span>
          <select
            className="rounded border border-zinc-800 bg-zinc-900 p-2"
            value={selectedModule}
            onChange={(event) => setSelectedModule(event.target.value)}
          >
            <option value="">Select module</option>
            {modules.map((moduleName) => (
              <option key={moduleName} value={moduleName}>
                {moduleName}
              </option>
            ))}
          </select>
        </label>
      </div>

      <ModuleOptsForm optsDoc={optsDoc} onChange={setCurrentOpts} />

      <div className="flex items-center gap-3">
        <button
          className="rounded bg-sky-600 px-4 py-2 text-sm font-medium text-white disabled:cursor-not-allowed disabled:bg-zinc-700"
          disabled={!selectedModule || !selectedOid || runState.loading}
          onClick={runModule}
        >
          {runState.loading ? "Running..." : "Run module"}
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
        <h2 className="mb-2 font-medium">Result</h2>
        <DepthJsonView data={hasFreshResult ? runState.result : null} />
      </div>
    </section>
  );
}
