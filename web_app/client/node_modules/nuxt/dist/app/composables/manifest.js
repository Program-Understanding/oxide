import { createMatcherFromExport, createRouter as createRadixRouter, toRouteMatcher } from "radix3";
import { defu } from "defu";
import { useRuntimeConfig } from "../nuxt.js";
import { appManifest as isAppManifestEnabled } from "#build/nuxt.config.mjs";
import { buildAssetsURL } from "#internal/nuxt/paths";
let manifest;
let matcher;
function fetchManifest() {
  if (!isAppManifestEnabled) {
    throw new Error("[nuxt] app manifest should be enabled with `experimental.appManifest`");
  }
  manifest = $fetch(buildAssetsURL(`builds/meta/${useRuntimeConfig().app.buildId}.json`), {
    responseType: "json"
  });
  manifest.then((m) => {
    matcher = createMatcherFromExport(m.matcher);
  }).catch((e) => {
    console.error("[nuxt] Error fetching app manifest.", e);
  });
  return manifest;
}
export function getAppManifest() {
  if (!isAppManifestEnabled) {
    throw new Error("[nuxt] app manifest should be enabled with `experimental.appManifest`");
  }
  return manifest || fetchManifest();
}
export async function getRouteRules(url) {
  if (import.meta.server) {
    const _routeRulesMatcher = toRouteMatcher(
      createRadixRouter({ routes: useRuntimeConfig().nitro.routeRules })
    );
    return defu({}, ..._routeRulesMatcher.matchAll(url).reverse());
  }
  await getAppManifest();
  if (!matcher) {
    console.error("[nuxt] Error creating app manifest matcher.", matcher);
    return {};
  }
  try {
    return defu({}, ...matcher.matchAll(url).reverse());
  } catch (e) {
    console.error("[nuxt] Error matching route rules.", e);
    return {};
  }
}
