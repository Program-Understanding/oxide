# oxide-app — Next.js Frontend for Oxide

A React + TypeScript frontend that talks to the Oxide REST API to let users browse collections, run analysis modules, and visualize results.

---

## Architecture overview

```
Browser (Next.js)
└── apiClient (lib/api/client.ts)
    └── HTTP → FastAPI backend (localhost:8000/api)
        └── Oxide Python runtime (src/oxide)
```

**Key design principle:** The frontend is purely a display layer. It never talks to Oxide directly — all data flows through the FastAPI adapter, which wraps the Oxide Python API.

---

## Project structure

```
oxide-app/
├── app/                          # Next.js App Router pages
│   ├── layout.tsx                # Root layout with Nav
│   ├── page.tsx                  # Home/overview page
│   ├── charts/page.tsx           # Charts page (file-level modules)
│   ├── module-runner/page.tsx    # Single-file module runner
│   └── collection-module-runner/ # Collection-level module runner
├── components/
│   ├── nav.tsx                   # Top navigation bar
│   ├── depth-json-view.tsx       # Generic JSON tree viewer
│   ├── module-opts-form.tsx      # Dynamic module options form
│   ├── file-dropzone.tsx         # File upload dropzone
│   ├── module-runner.tsx          # Single-file execution UI
│   ├── collection-manager.tsx     # Collection CRUD UI
│   ├── collection-module-runner.tsx # Collection-level execution UI
│   ├── charts-workspace.tsx       # Charts page orchestration
│   └── charts/
│       ├── chart-renderers.tsx   # Module-to-renderer dispatcher
│       └── renderers/
│           ├── triage-renderer.tsx         # Donut chart for triage module
│           ├── cyclo-complexity-renderer.tsx # Horizontal bar chart
│           ├── entropy-renderer.tsx         # Line chart
│           ├── histogram-renderer.tsx        # Bar chart (byte/opcode freq)
│           ├── heatmap-renderer.tsx          # N-gram heatmap
│           ├── call-graph-renderer.tsx      # Cytoscape call graph
│           ├── control-flow-renderer.tsx     # Cytoscape CFG
│           ├── binary-visualizer-renderer.tsx # Canvas grid
│           ├── chartjs-setup.ts             # Chart.js registration
│           ├── cytoscape-loader.ts           # Cytoscape lazy loader
│           ├── types.ts                      # Renderer prop types
│           └── utils.ts                      # Shared helpers (getModuleResult, toEntries, etc.)
├── lib/api/
│   ├── client.ts                 # All HTTP calls to backend
│   └── types.ts                  # Shared TypeScript types
└── types/                        # Type shims for packages without .d.ts
```

---

## API client (`lib/api/client.ts`)

All HTTP calls go through the `apiClient` object. It reads `NEXT_PUBLIC_API_BASE_URL` from env (defaults to `http://localhost:8000/api`).

Key methods:

| Method | Purpose |
|--------|---------|
| `getModules()` | List all available Oxide modules |
| `getChartCapabilities()` | List which chart modules are available |
| `getCollections()` | List all collections |
| `getCollectionFiles(name)` | Get files in a collection |
| `retrieve(payload)` | Run any module (oid, oids, or collection) |
| `getModuleDocumentation(name)` | Get module opts_doc and description |
| `uploadFiles(files)` | Import files into Oxide |
| `createCollection(payload)` | Create a named OID collection |
| `flushOid(oid)` | Delete all data for an OID |

### `retrieve()` payload shape

```typescript
// Single file
{ module: "entropy_graph", oid: "abc123...", opts: {} }

// Multiple files
{ module: "entropy_graph", oids: ["abc...", "def..."], opts: {} }

// Entire collection
{ module: "entropy_graph", collection: "malware_set", opts: {} }
```

### `retrieve()` response envelope

```json
{
  "module": "entropy_graph",
  "target": { "type": "oid", "oid": "..." },
  "results": { ... module-specific data ... }
}
```

---

## Adding a new page

1. Create `app/my-page/page.tsx` with a default export.
2. Import and use existing components as needed.
3. Add a link to `components/nav.tsx`.

---

## Adding a new chart renderer

When a new module produces visual output, follow this checklist:

### 1. Register the module in the backend

Edit `web_interface/Oxide-Formula/routes/modules.py` → `REQUIRED_CHART_MODULES`:

```python
REQUIRED_CHART_MODULES = [
    ...
    "my_new_module",   # ← add here
]
```

This makes it appear in the chart module dropdown.

### 2. Create the renderer

Create `components/charts/renderers/my-new-module-renderer.tsx`:

```typescript
"use client";

import { ensureChartJsRegistered } from "./chartjs-setup";
ensureChartJsRegistered();

export function MyNewModuleRenderer({ data }: { data: unknown }) {
  if (!data) return <p>No data available.</p>;
  // Parse data, render Chart.js or Cytoscape, etc.
  return <div>...</div>;
}
```

### 3. Wire it into the dispatcher

Edit `components/charts/chart-renderers.tsx`:

```typescript
import { MyNewModuleRenderer } from "./renderers/my-new-module-renderer";

// In ChartRenderer function:
if (moduleName === "my_new_module") return <MyNewModuleRenderer data={moduleData} />;
```

### 4. Handle module-specific data shapes

The `ChartRenderer` calls `getModuleResult(result, oid)` from `renderers/utils.ts`. This extracts the right slice from the response for per-file charts (handles both flat and OID-keyed result shapes). For collection-only modules (like `triage`), pass the raw `result` directly.

---

## Chart rendering patterns

### Chart.js (line, bar, doughnut, etc.)

- Register components in `chartjs-setup.ts`
- Use `ensureChartJsRegistered()` in your renderer
- Use `react-chartjs-2` `<Line>`, `<Bar>`, `<Doughnut>`, etc.
- Use `useRef<ChartJS<"bar">>` for imperative control (reset, export)
- Prefer `maintainAspectRatio: true` and size constraints (`max-w-sm`, etc.)

### Cytoscape (call graphs, CFGs)

- Use `dynamic(() => import("cytoscape"), { ssr: false })` to avoid SSR issues
- Use the shared `renderCytoscape` utility or pattern from existing renderers
- Use `types/cytoscape-dagre.d.ts` for layout type support

### Canvas (binary visualizer)

- Use a plain `<canvas>` ref with 2D context
- Handle resize with `ResizeObserver`

---

## Running locally

### Prerequisites

- Node `>=20.9.0` (required — not just recommended)
- Backend running at `http://localhost:8000/api`

### Setup

```bash
# 1. Start the backend
cd web_interface/Oxide-Formula
pip install -r requirements.txt
./api_server.sh   # runs uvicorn on port 8000

# 2. Start the frontend (in a separate terminal)
cd web_interface/oxide-app
cp .env.example .env.local   # already defaults to localhost:8000/api
npm install
./web_app.sh                 # runs Next.js dev server on port 3000
```

### Environment

```bash
# .env.example / .env.local
NEXT_PUBLIC_API_BASE_URL=http://localhost:8000/api
```

### Build check

```bash
npm run build:node20
```

---

## Dependencies

| Package | Purpose |
|--------|---------|
| `next` | App framework |
| `react`, `react-dom` | UI |
| `chart.js`, `react-chartjs-2` | Charts (line, bar, doughnut, heatmap) |
| `chartjs-chart-matrix` | Matrix/heatmap cells |
| `chartjs-plugin-zoom` | Pan/zoom on charts |
| `cytoscape` | Graph visualizations (call graph, CFG) |
| `cytoscape-dagre` | DAG layout for graphs |

---

## Key conventions

- All API calls use `cache: "no-store"` to avoid stale data
- Components that use Chart.js/Cytoscape are `"use client"` and use `dynamic()` imports with `ssr: false` in the parent
- Module options (`opts_doc`) are typed as `{ type, mangle, default }` in both backend Pydantic models and frontend `OptEntry`
- Result normalization happens server-side: sets → arrays, tuples → arrays, NetworkX graphs → node-link JSON, dicts → plain objects
