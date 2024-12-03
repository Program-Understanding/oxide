'use strict';

const defu = require('defu');
const vue = require('vue');
const useHead = require('./shared/vue.104c41b5.cjs');
const injectHead = require('./shared/vue.6b1572ee.cjs');
require('unhead');
require('@unhead/shared');

const UnheadPlugin = (_Vue) => {
  _Vue.config.optionMergeStrategies.head = function(toVal, fromVal, vm) {
    if (typeof toVal === "function") {
      toVal = toVal.call(vm || this || _Vue);
    }
    if (typeof fromVal === "function") {
      fromVal = fromVal.call(vm || this || _Vue);
    }
    return defu.defu(toVal, fromVal);
  };
  _Vue.mixin({
    created() {
      let source = false;
      if (injectHead.Vue3) {
        const instance = vue.getCurrentInstance();
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
        useHead.useHead(source);
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
            [injectHead.headSymbol]: options.unhead
          };
        };
      }
    }
  });
};

exports.UnheadPlugin = UnheadPlugin;
