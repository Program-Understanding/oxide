export interface OptEntry {
  type: "str" | "int" | "bool";
  mangle: boolean;
  default: string | number | boolean | null;
}

export interface ModuleDocumentation {
  description: string;
  opts_doc: Record<string, OptEntry>;
}

export interface ModulesResponse {
  modules: string[];
}

export interface ImportedFile {
  name: string;
  oid: string;
  success: boolean;
  error: string | null;
}

export interface UploadResponse {
  uploaded: ImportedFile[];
  failed: ImportedFile[];
  total: number;
}

export interface CreateCollectionRequest {
  name: string;
  oid_list: string[];
  notes?: string;
}

export interface CreateCollectionResponse {
  name: string;
  cid: string;
  oid_count: number;
}

export interface CollectionsResponse {
  collections: string[];
}

export interface CollectionFile {
  oid: string;
  names: string[];
}

export interface CollectionFilesResponse {
  collection: string;
  cid: string;
  files: CollectionFile[];
}

export interface ModuleCapability {
  module: string;
  available: boolean;
}

export interface ChartCapabilitiesResponse {
  required_chart_modules: ModuleCapability[];
}

export interface RetrieveRequest {
  module: string;
  oid?: string;
  oids?: string[];
  collection?: string;
  opts?: Record<string, unknown>;
}

export interface RetrieveResponse {
  module: string;
  target: Record<string, unknown>;
  results: unknown;
}
