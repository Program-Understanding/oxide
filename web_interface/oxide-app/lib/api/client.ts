import {
  ChartCapabilitiesResponse,
  CollectionFilesResponse,
  CollectionsResponse,
  ModulesResponse,
  RetrieveRequest,
  RetrieveResponse,
} from "./types";

const API_BASE_URL =
  process.env.NEXT_PUBLIC_API_BASE_URL ?? "http://localhost:8000/api";

async function requestJson<T>(path: string, init?: RequestInit): Promise<T> {
  const response = await fetch(`${API_BASE_URL}${path}`, {
    ...init,
    headers: {
      "Content-Type": "application/json",
      ...(init?.headers ?? {}),
    },
    cache: "no-store",
  });

  if (!response.ok) {
    const body = await response.text();
    throw new Error(`${response.status} ${response.statusText}: ${body}`);
  }

  return (await response.json()) as T;
}

export const apiClient = {
  async getModules() {
    const response = await requestJson<ModulesResponse>("/modules/");
    return {
      ...response,
      modules: Array.from(new Set(response.modules)),
    };
  },

  getCollections() {
    return requestJson<CollectionsResponse>("/collections/");
  },

  getCollectionFiles(collectionName: string) {
    return requestJson<CollectionFilesResponse>(
      `/collections/${encodeURIComponent(collectionName)}/files`,
    );
  },

  getChartCapabilities() {
    return requestJson<ChartCapabilitiesResponse>("/modules/chart-capabilities");
  },

  retrieve(payload: RetrieveRequest) {
    return requestJson<RetrieveResponse>("/analysis/retrieve", {
      method: "POST",
      body: JSON.stringify(payload),
    });
  },
};
