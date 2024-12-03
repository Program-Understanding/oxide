// index.ts
import { components, directives } from "@primevue/metadata";
function PrimeVueResolver(options = {}) {
  const getName = (name, prefix) => {
    if (prefix) {
      if (!name.startsWith(prefix)) return;
      name = name.substring(prefix.length);
    }
    return name;
  };
  return [
    {
      type: "component",
      resolve: (name) => {
        var _a;
        const { prefix } = options.components || {};
        const cName = getName(name, prefix);
        const cMeta = components.find((c) => c.name.toLocaleLowerCase() === (cName == null ? void 0 : cName.toLocaleLowerCase()));
        if (cMeta) {
          return ((_a = options == null ? void 0 : options.resolve) == null ? void 0 : _a.call(options, cMeta, "component")) ?? {
            from: cMeta.from
          };
        }
      }
    },
    {
      type: "directive",
      resolve: (name) => {
        var _a;
        const { prefix } = options.directives || {};
        const dName = getName(name, prefix);
        const dMeta = directives.find((d) => d.name.toLocaleLowerCase() === (dName == null ? void 0 : dName.toLocaleLowerCase()));
        if (dMeta) {
          return ((_a = options == null ? void 0 : options.resolve) == null ? void 0 : _a.call(options, dMeta, "directive")) ?? {
            as: dMeta.as,
            from: dMeta.from
          };
        }
      }
    }
  ];
}
export {
  PrimeVueResolver
};
