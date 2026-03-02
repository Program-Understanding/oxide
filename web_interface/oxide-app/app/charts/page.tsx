import { apiClient } from "@/lib/api/client";
import { ChartsWorkspace } from "@/components/charts-workspace";

export default async function ChartsPage() {
  const capabilities = await apiClient
    .getChartCapabilities()
    .catch(() => ({ required_chart_modules: [] }));

  return (
    <section className="space-y-4">
      <h1 className="text-2xl font-semibold">Charts</h1>
      <p className="text-zinc-300">Collection/file/chart selection and execution.</p>
      <ChartsWorkspace capabilities={capabilities.required_chart_modules} />
    </section>
  );
}
