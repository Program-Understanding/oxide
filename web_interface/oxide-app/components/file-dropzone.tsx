"use client";

import { useCallback, useRef, useState } from "react";
import { apiClient } from "@/lib/api/client";
import type { ImportedFile, UploadResponse } from "@/lib/api/types";

type FileDropzoneProps = {
  onUploadComplete: (results: UploadResponse, newCollectionName: string) => void;
};

export function FileDropzone({ onUploadComplete }: FileDropzoneProps) {
  const [isDragging, setIsDragging] = useState(false);
  const [isUploading, setIsUploading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [results, setResults] = useState<UploadResponse | null>(null);
  const [lastCollection, setLastCollection] = useState<string>("");
  const [isClearing, setIsClearing] = useState(false);
  const inputRef = useRef<HTMLInputElement>(null);

  const uploadFiles = useCallback(
    async (files: File[]) => {
      if (!files.length) return;

      setIsUploading(true);
      setError(null);
      setResults(null);

      try {
        const result = await apiClient.uploadFiles(files);
        setResults(result);

        if (result.uploaded.length > 0) {
          const oids = result.uploaded.map((f) => f.oid);
          const timestamp = new Date().toISOString().slice(0, 19).replace(/[T:]/g, "-");
          const collectionName = `upload-${timestamp}`;
          try {
            const colResult = await apiClient.createCollection({
              name: collectionName,
              oid_list: oids,
              notes: `Uploaded ${oids.length} file(s) via web UI`,
            });
            setLastCollection(colResult.name);
            onUploadComplete(result, colResult.name);
          } catch {
            setLastCollection(collectionName);
            onUploadComplete(result, "");
          }
        } else {
          onUploadComplete(result, "");
        }
      } catch (err) {
        setError(err instanceof Error ? err.message : "Upload failed");
      } finally {
        setIsUploading(false);
      }
    },
    [onUploadComplete],
  );

  const handleClear = useCallback(async () => {
    if (!lastCollection) return;
    setIsClearing(true);
    try {
      await apiClient.deleteCollection(lastCollection);
      setResults(null);
      setLastCollection("");
      onUploadComplete({ uploaded: [], failed: [], total: 0 }, "");
    } catch {
      setError("Failed to clear collection");
    } finally {
      setIsClearing(false);
    }
  }, [lastCollection, onUploadComplete]);

  const handleDrop = useCallback(
    (e: React.DragEvent) => {
      e.preventDefault();
      setIsDragging(false);
      const files = Array.from(e.dataTransfer.files);
      void uploadFiles(files);
    },
    [uploadFiles],
  );

  const handleDragOver = useCallback((e: React.DragEvent) => {
    e.preventDefault();
    setIsDragging(true);
  }, []);

  const handleDragLeave = useCallback(() => {
    setIsDragging(false);
  }, []);

  const handleInputChange = useCallback(
    (e: React.ChangeEvent<HTMLInputElement>) => {
      const files = Array.from(e.target.files ?? []);
      void uploadFiles(files);
      // Reset so same file can be re-selected
      if (inputRef.current) inputRef.current.value = "";
    },
    [uploadFiles],
  );

  const handleClick = useCallback(() => {
    inputRef.current?.click();
  }, []);

  return (
    <div className="space-y-2">
      <div
        className={`flex cursor-pointer flex-col items-center justify-center rounded border-2 border-dashed p-6 transition-colors ${
          isDragging
            ? "border-sky-500 bg-sky-950/20"
            : "border-zinc-700 hover:border-zinc-500"
        }`}
        onClick={handleClick}
        onDrop={handleDrop}
        onDragOver={handleDragOver}
        onDragLeave={handleDragLeave}
      >
        <input
          ref={inputRef}
          type="file"
          multiple
          className="hidden"
          onChange={handleInputChange}
        />
        {isUploading ? (
          <p className="text-sm text-zinc-400">Uploading...</p>
        ) : (
          <>
            <p className="text-sm font-medium text-zinc-300">
              Drop binary files here or click to browse
            </p>
            <p className="text-xs text-zinc-500">Any file type, up to 20 at a time</p>
          </>
        )}
      </div>

      {error && (
        <p className="text-sm text-red-400">{error}</p>
      )}

      {results && (
        <div className="space-y-1">
          {results.uploaded.map((f) => (
            <div key={f.oid} className="flex items-center justify-between rounded bg-zinc-900 px-3 py-1 text-xs">
              <span className="truncate text-zinc-300" title={f.name}>
                {f.name}
              </span>
              <span className="ml-2 shrink-0 font-mono text-zinc-500">{f.oid.slice(0, 8)}…</span>
            </div>
          ))}
          {results.failed.map((f, i) => (
            <div key={i} className="flex items-center justify-between rounded bg-red-950/30 px-3 py-1 text-xs">
              <span className="truncate text-red-300" title={f.name}>
                {f.name}
              </span>
              <span className="ml-2 shrink-0 text-red-400">{f.error}</span>
            </div>
          ))}
          <p className="text-xs text-zinc-500">
            Imported {results.uploaded.length} of {results.total} file
            {results.total !== 1 ? "s" : ""}
            {results.failed.length > 0 && `, ${results.failed.length} failed`}
          </p>
        </div>
      )}

      {lastCollection && (
        <button
          className="w-full rounded border border-red-700 bg-red-950/30 px-3 py-1.5 text-xs text-red-300 transition-colors hover:bg-red-900/50 disabled:cursor-not-allowed disabled:opacity-50"
          disabled={isClearing}
          onClick={(e) => {
            e.stopPropagation();
            void handleClear();
          }}
        >
          {isClearing ? "Clearing..." : `Clear upload collection (${lastCollection})`}
        </button>
      )}
    </div>
  );
}