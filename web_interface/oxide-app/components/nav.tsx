import Link from "next/link";

const links = [
  { href: "/", label: "Home" },
  { href: "/module-runner", label: "Module Runner" },
  { href: "/collection-module-runner", label: "Collection Module Runner" },
  { href: "/charts", label: "Charts" },
];

export function Nav() {
  return (
    <nav className="border-b border-zinc-800 bg-zinc-900/60 backdrop-blur">
      <div className="mx-auto flex w-full max-w-[min(1800px,98vw)] gap-6 px-4 py-4 sm:px-6">
        {links.map((link) => (
          <Link key={link.href} href={link.href} className="text-sm font-medium text-zinc-200 hover:text-white">
            {link.label}
          </Link>
        ))}
      </div>
    </nav>
  );
}
