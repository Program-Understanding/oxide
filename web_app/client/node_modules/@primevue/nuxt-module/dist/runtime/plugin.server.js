import { styles, stylesToTop, themes } from "#primevue-style";
const defineNitroPlugin = (def) => def;
export default defineNitroPlugin(async (nitroApp) => {
  nitroApp.hooks.hook("render:html", (html) => {
    html.head.unshift(stylesToTop);
    html.head.push(styles);
    html.head.push(themes);
  });
});
