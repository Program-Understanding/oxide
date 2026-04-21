import { CollectionModuleRunner } from "@/components/collection-module-runner";

export default function CollectionModuleRunnerPage() {
  return (
    <section className="space-y-4">
      <h1 className="text-2xl font-semibold">Collection Module Runner</h1>
      <p className="text-zinc-400">Run a module across all files in a collection and view aggregated results.</p>
      <CollectionModuleRunner />
    </section>
  );
}