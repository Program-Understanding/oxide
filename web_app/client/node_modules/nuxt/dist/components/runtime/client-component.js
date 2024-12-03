import { defineAsyncComponent, defineComponent, h } from "vue";
import ClientOnly from "#app/components/client-only";
export const createClientPage = /* @__NO_SIDE_EFFECTS__ */ (loader) => {
  const page = defineAsyncComponent(import.meta.dev ? () => loader().then((m) => {
    (m.default || m).__clientOnlyPage = true;
    return m.default || m;
  }) : loader);
  return defineComponent({
    inheritAttrs: false,
    setup(_, { attrs }) {
      return () => h("div", [
        h(ClientOnly, void 0, {
          default: () => h(page, attrs)
        })
      ]);
    }
  });
};
