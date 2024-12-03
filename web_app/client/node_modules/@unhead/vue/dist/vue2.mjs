import { defu } from 'defu';
import { getCurrentInstance } from 'vue';
import { u as useHead } from './shared/vue.8fc199ce.mjs';
import { V as Vue3, h as headSymbol } from './shared/vue.f49591ad.mjs';
import 'unhead';
import '@unhead/shared';

const UnheadPlugin = (_Vue) => {
  _Vue.config.optionMergeStrategies.head = function(toVal, fromVal, vm) {
    if (typeof toVal === "function") {
      toVal = toVal.call(vm || this || _Vue);
    }
    if (typeof fromVal === "function") {
      fromVal = fromVal.call(vm || this || _Vue);
    }
    return defu(toVal, fromVal);
  };
  _Vue.mixin({
    created() {
      let source = false;
      if (Vue3) {
        const instance = getCurrentInstance();
        if (!instance)
          return;
        const options = instance.type;
        if (!options || !("head" in options))
          return;
        source = typeof options.head === "function" ? () => options.head.call(instance.proxy) : options.head;
      } else {
        const head = this.$options.head;
        if (head) {
          source = typeof head === "function" ? () => head.call(this) : head;
        }
      }
      if (source) {
        useHead(source);
      }
    },
    beforeCreate() {
      const options = this.$options;
      if (options.unhead) {
        const origProvide = options.provide;
        options.provide = function() {
          let origProvideResult;
          if (typeof origProvide === "function")
            origProvideResult = origProvide.call(this);
          else
            origProvideResult = origProvide || {};
          return {
            ...origProvideResult,
            [headSymbol]: options.unhead
          };
        };
      }
    }
  });
};

export { UnheadPlugin };
