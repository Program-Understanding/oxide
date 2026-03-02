import type { Metadata } from "next";
import "./globals.css";
import { Nav } from "@/components/nav";

export const metadata: Metadata = {
  title: "Oxide App",
  description: "Next frontend for Oxide",
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>
        <Nav />
        <main className="mx-auto w-full max-w-[min(1800px,98vw)] px-4 py-6 sm:px-6 sm:py-8">{children}</main>
      </body>
    </html>
  );
}
