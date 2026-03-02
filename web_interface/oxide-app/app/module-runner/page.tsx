import { ModuleRunner } from "@/components/module-runner";

export default function ModuleRunnerPage() {
  return (
    <section className="space-y-4">
      <h1 className="text-2xl font-semibold">Module Runner</h1>
      <p className="text-zinc-300">Collection → file → module execution.</p>
      <ModuleRunner />
    </section>
  );
}
