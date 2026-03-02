import Link from "next/link";

const links = [
  { href: "/", label: "Home" },
  { href: "/module-runner", label: "Module Runner" },
  { href: "/charts", label: "Charts" },
];

export function Nav() {
  return (
    <nav className="border-b border-zinc-800 bg-zinc-900/60 backdrop-blur">
      <div className="mx-auto flex max-w-6xl gap-6 px-6 py-4">
        {links.map((link) => (
          <Link key={link.href} href={link.href} className="text-sm font-medium text-zinc-200 hover:text-white">
            {link.label}
          </Link>
        ))}
      </div>
    </nav>
  );
}
