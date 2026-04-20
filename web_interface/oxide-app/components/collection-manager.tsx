"use client";

import { useCallback, useState } from "react";
import { apiClient } from "@/lib/api/client";
import type { CollectionFile, CollectionFilesResponse } from "@/lib/api/types";

type CollectionManagerProps = {
  onCollectionDeleted?: () => void;
};

export function CollectionManager({ onCollectionDeleted }: CollectionManagerProps) {
  const [collections, setCollections] = useState<string[]>([]);
  const [selectedCollection, setSelectedCollection] = useState<string>("");
  const [files, setFiles] = useState<CollectionFile[]>([]);
  const [selectedOids, setSelectedOids] = useState<Set<string>>(new Set());
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [deletingCollection, setDeletingCollection] = useState(false);
  const [deletingOids, setDeletingOids] = useState(false);

  const loadCollections = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const resp = await apiClient.getCollections();
      setCollections(resp.collections);
    } catch {
      setError("Failed to load collections");
    } finally {
      setLoading(false);
    }
  }, []);

  const loadFiles = useCallback(async (colName: string) => {
    setLoading(true);
    setError(null);
    setSelectedOids(new Set());
    try {
      const resp = await apiClient.getCollectionFiles(colName);
      setFiles(resp.files);
    } catch {
      setError("Failed to load files");
      setFiles([]);
    } finally {
      setLoading(false);
    }
  }, []);

  const handleCollectionChange = useCallback(
    (name: string) => {
      setSelectedCollection(name);
      if (name) {
        void loadFiles(name);
      } else {
        setFiles([]);
      }
    },
    [loadFiles],
  );

  const toggleOid = useCallback((oid: string) => {
    setSelectedOids((prev) => {
      const next = new Set(prev);
      if (next.has(oid)) {
        next.delete(oid);
      } else {
        next.add(oid);
      }
      return next;
    });
  }, []);

  const toggleAll = useCallback(() => {
    setSelectedOids((prev) => {
      if (prev.size === files.length) {
        return new Set();
      }
      return new Set(files.map((f) => f.oid));
    });
  }, [files]);

  const handleDeleteCollection = useCallback(async () => {
    if (!selectedCollection) return;
    setDeletingCollection(true);
    setError(null);
    try {
      await apiClient.deleteCollection(selectedCollection);
      setSelectedCollection("");
      setFiles([]);
      void loadCollections();
      onCollectionDeleted?.();
    } catch {
      setError("Failed to delete collection");
    } finally {
      setDeletingCollection(false);
    }
  }, [selectedCollection, loadCollections, onCollectionDeleted]);

  const handleDeleteSelectedOids = useCallback(async () => {
    if (!selectedCollection || selectedOids.size === 0) return;
    setDeletingOids(true);
    setError(null);
    try {
      await apiClient.deleteOidsFromCollection(selectedCollection, Array.from(selectedOids));
      void loadFiles(selectedCollection);
      setSelectedOids(new Set());
    } catch {
      setError("Failed to delete OIDs");
    } finally {
      setDeletingOids(false);
    }
  }, [selectedCollection, selectedOids, loadFiles]);

  return (
    <div className="space-y-3 rounded border border-zinc-800 p-4">
      <div className="flex items-center justify-between">
        <h3 className="font-medium">Collection Manager</h3>
        <button
          className="rounded bg-zinc-800 px-3 py-1 text-xs text-zinc-300 transition-colors hover:bg-zinc-700 disabled:opacity-50"
          disabled={loading}
          onClick={() => void loadCollections()}
        >
          Refresh
        </button>
      </div>

      {error && (
        <p className="text-sm text-red-400">{error}</p>
      )}

      <div className="flex items-center gap-2">
        <select
          className="flex-1 rounded border border-zinc-800 bg-zinc-900 p-2 text-sm"
          value={selectedCollection}
          onChange={(e) => void handleCollectionChange(e.target.value)}
        >
          <option value="">Select collection...</option>
          {collections.map((col) => (
            <option key={col} value={col}>
              {col}
            </option>
          ))}
        </select>

        {selectedCollection && (
          <button
            className="rounded border border-red-700 bg-red-950/30 px-3 py-1.5 text-xs text-red-300 transition-colors hover:bg-red-900/50 disabled:opacity-50"
            disabled={deletingCollection}
            onClick={() => void handleDeleteCollection()}
          >
            {deletingCollection ? "Deleting..." : "Delete collection"}
          </button>
        )}
      </div>

      {files.length > 0 && (
        <>
          <div className="flex items-center justify-between">
            <p className="text-xs text-zinc-500">
              {files.length} file{files.length !== 1 ? "s" : ""}
              {selectedOids.size > 0 && ` — ${selectedOids.size} selected`}
            </p>
            <div className="flex gap-2">
              <button
                className="rounded bg-zinc-800 px-2 py-1 text-xs text-zinc-300 transition-colors hover:bg-zinc-700"
                onClick={() => void toggleAll()}
              >
                {selectedOids.size === files.length ? "Deselect all" : "Select all"}
              </button>
              <button
                className="rounded border border-red-700 bg-red-950/30 px-2 py-1 text-xs text-red-300 transition-colors hover:bg-red-900/50 disabled:opacity-50"
                disabled={selectedOids.size === 0 || deletingOids}
                onClick={() => void handleDeleteSelectedOids()}
              >
                {deletingOids ? "Deleting..." : `Delete selected (${selectedOids.size})`}
              </button>
            </div>
          </div>

          <div className="max-h-64 space-y-1 overflow-y-auto">
            {files.map((file) => (
              <div
                key={file.oid}
                className={`flex cursor-pointer items-center gap-2 rounded px-2 py-1 text-xs transition-colors ${
                  selectedOids.has(file.oid)
                    ? "bg-sky-900/30 border border-sky-600"
                    : "bg-zinc-900 hover:bg-zinc-800"
                }`}
                onClick={() => void toggleOid(file.oid)}
              >
                <input
                  type="checkbox"
                  checked={selectedOids.has(file.oid)}
                  onChange={() => void toggleOid(file.oid)}
                  onClick={(e) => e.stopPropagation()}
                  className="shrink-0"
                />
                <span className="truncate text-zinc-300" title={file.names.join(", ")}>
                  {file.names[0] ?? file.oid}
                </span>
                <span className="ml-auto shrink-0 font-mono text-zinc-500">{file.oid.slice(0, 8)}…</span>
              </div>
            ))}
          </div>
        </>
      )}

      {!loading && selectedCollection && files.length === 0 && (
        <p className="text-xs text-zinc-500">No files in this collection.</p>
      )}
    </div>
  );
}