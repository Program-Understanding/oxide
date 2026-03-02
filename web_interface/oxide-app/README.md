# oxide-app (Next.js Frontend)

This is the frontend for Oxide, rewritten from the previous Vue/Nuxt UI to **Next.js + React + TypeScript**.

## Project structure (implementation map)

- `app/`
	- route-level pages (`/`, `/module-runner`, `/charts`)
- `components/module-runner.tsx`
	- module execution UI and state logic
- `components/charts-workspace.tsx`
	- chart execution UI and gating
- `components/charts/chart-renderers.tsx`
	- thin dispatcher for chart modules
- `components/charts/renderers/*`
	- module-specific renderers and shared chart utilities
- `lib/api/types.ts`
	- shared frontend API types
- `lib/api/client.ts`
	- HTTP client and endpoint wrappers
- `types/`
	- local type shims for packages requiring declarations

## Runtime requirements

- Node `>=20.9.0` (recommended 20.x)
- backend running at `http://localhost:8000/api` (or custom base URL)

Environment:

```bash
cp .env.example .env.local
```

`.env.example`:

```dotenv
NEXT_PUBLIC_API_BASE_URL=http://localhost:8000/api
```

## Run locally

1. Start backend (`web_interface/Oxide-Formula`)
2. Install frontend deps:

```bash
npm install
```

3. Start frontend:

```bash
./web_app.sh
```

If your system Node is older than 20, use:

```bash
npm run dev:node20
```

Build check:

```bash
npm run build:node20
```

