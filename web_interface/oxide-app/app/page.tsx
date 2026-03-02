export default function HomePage() {
  return (
    <section className="space-y-4">
      <h1 className="text-2xl font-semibold">Oxide Frontend Rewrite</h1>
      <p className="text-zinc-300">Use Module Runner and Charts pages</p>
      <ul className="list-disc pl-6 text-zinc-300">
        <li>Backend contract: REST endpoints under <code>/api</code></li>
        <li>Typed API client added in <code>lib/api/client.ts</code></li>
      </ul>
    </section>
  );
}
