"use strict";Object.defineProperty(exports, "__esModule", {value: true}); function _optionalChain(ops) { let lastAccessLHS = undefined; let value = ops[0]; let i = 1; while (i < ops.length) { const op = ops[i]; const fn = ops[i + 1]; i += 2; if ((op === 'optionalAccess' || op === 'optionalCall') && value == null) { return undefined; } if (op === 'access' || op === 'optionalAccess') { lastAccessLHS = value; value = fn(value); } else if (op === 'call' || op === 'optionalCall') { value = fn((...args) => value.call(lastAccessLHS, ...args)); lastAccessLHS = undefined; } } return value; }

var _chunkMECUHPJXcjs = require('./chunk-MECUHPJX.cjs');

// src/data-loaders/defineLoader.ts



var _vuerouter = require('vue-router');












var _runtime = require('unplugin-vue-router/runtime');
var _vue = require('vue');
function defineBasicLoader(nameOrLoader, _loaderOrOptions, opts) {
  const loader = typeof nameOrLoader === "function" ? nameOrLoader : _loaderOrOptions;
  opts = typeof _loaderOrOptions === "object" ? _loaderOrOptions : opts;
  const options = {
    ...DEFAULT_DEFINE_LOADER_OPTIONS,
    ...opts,
    // avoid opts overriding with `undefined`
    commit: _optionalChain([opts, 'optionalAccess', _2 => _2.commit]) || DEFAULT_DEFINE_LOADER_OPTIONS.commit
  };
  function load(to, router, from, parent) {
    const entries = router[_runtime.LOADER_ENTRIES_KEY];
    const isSSR = router[_runtime.IS_SSR_KEY];
    if (!entries.has(loader)) {
      entries.set(loader, {
        // force the type to match
        data: _vue.shallowRef.call(void 0, ),
        isLoading: _vue.shallowRef.call(void 0, false),
        error: _vue.shallowRef.call(void 0, ),
        to,
        options,
        children: /* @__PURE__ */ new Set(),
        resetPending() {
          this.pendingLoad = null;
          this.pendingTo = null;
        },
        pendingLoad: null,
        pendingTo: null,
        staged: _runtime.STAGED_NO_VALUE,
        stagedError: null,
        commit
      });
    }
    const entry = entries.get(loader);
    if (entry.pendingTo === to && entry.pendingLoad) {
      return entry.pendingLoad;
    }
    const { error, isLoading, data } = entry;
    const initialRootData = router[INITIAL_DATA_KEY];
    const key = options.key || "";
    let initialData = _runtime.STAGED_NO_VALUE;
    if (initialRootData && key in initialRootData) {
      initialData = initialRootData[key];
      delete initialRootData[key];
    }
    if (initialData !== _runtime.STAGED_NO_VALUE) {
      data.value = initialData;
      return entry.pendingLoad = Promise.resolve();
    }
    entry.pendingTo = to;
    isLoading.value = true;
    const currentContext = _runtime.getCurrentContext.call(void 0, );
    if (process.env.NODE_ENV === "development") {
      if (parent !== currentContext[0]) {
        console.warn(
          `\u274C\u{1F476} "${options.key}" has a different parent than the current context. This shouldn't be happening. Please report a bug with a reproduction to https://github.com/posva/unplugin-vue-router/`
        );
      }
    }
    _runtime.setCurrentContext.call(void 0, [entry, router, to]);
    entry.staged = _runtime.STAGED_NO_VALUE;
    entry.stagedError = error.value;
    const currentLoad = Promise.resolve(
      loader(to, { signal: _optionalChain([to, 'access', _3 => _3.meta, 'access', _4 => _4[_runtime.ABORT_CONTROLLER_KEY], 'optionalAccess', _5 => _5.signal]) })
    ).then((d) => {
      if (entry.pendingLoad === currentLoad) {
        if (d instanceof _runtime.NavigationResult) {
          to.meta[_runtime.NAVIGATION_RESULTS_KEY].push(d);
        } else {
          entry.staged = d;
          entry.stagedError = null;
        }
      }
    }).catch((e) => {
      if (entry.pendingLoad === currentLoad) {
        entry.stagedError = e;
        if (!_chunkMECUHPJXcjs.toLazyValue.call(void 0, options.lazy, to, from) || isSSR) {
          throw e;
        }
      }
    }).finally(() => {
      _runtime.setCurrentContext.call(void 0, currentContext);
      if (entry.pendingLoad === currentLoad) {
        isLoading.value = false;
        if (options.commit === "immediate" || // outside of navigation
        !router[_runtime.PENDING_LOCATION_KEY]) {
          entry.commit(to);
        }
      } else {
      }
    });
    _runtime.setCurrentContext.call(void 0, currentContext);
    entry.pendingLoad = currentLoad;
    return currentLoad;
  }
  function commit(to) {
    if (this.pendingTo === to) {
      if (process.env.NODE_ENV === "development") {
        if (this.staged === _runtime.STAGED_NO_VALUE) {
          console.warn(
            `Loader "${options.key}"'s "commit()" was called but there is no staged data.`
          );
        }
      }
      if (this.staged !== _runtime.STAGED_NO_VALUE) {
        this.data.value = this.staged;
      }
      this.error.value = this.stagedError;
      this.staged = _runtime.STAGED_NO_VALUE;
      this.stagedError = this.error.value;
      this.pendingTo = null;
      this.to = to;
      for (const childEntry of this.children) {
        childEntry.commit(to);
      }
    }
  }
  const useDataLoader = () => {
    const currentContext = _runtime.getCurrentContext.call(void 0, );
    const [parentEntry, _router, _route] = currentContext;
    const router = _router || _vuerouter.useRouter.call(void 0, );
    const route = _route || _vuerouter.useRoute.call(void 0, );
    const entries = router[_runtime.LOADER_ENTRIES_KEY];
    let entry = entries.get(loader);
    if (
      // if the entry doesn't exist, create it with load and ensure it's loading
      !entry || // the existing pending location isn't good, we need to load again
      parentEntry && entry.pendingTo !== route
    ) {
      router[_runtime.APP_KEY].runWithContext(
        () => load(route, router, void 0, parentEntry)
      );
    }
    entry = entries.get(loader);
    if (parentEntry) {
      if (parentEntry === entry) {
        console.warn(
          `\u{1F476}\u274C "${options.key}" has itself as parent. This shouldn't be happening. Please report a bug with a reproduction to https://github.com/posva/unplugin-vue-router/`
        );
      }
      parentEntry.children.add(entry);
    }
    const { data, error, isLoading } = entry;
    const useDataLoaderResult = {
      data,
      error,
      isLoading,
      reload: (to = router.currentRoute.value) => router[_runtime.APP_KEY].runWithContext(() => load(to, router)).then(
        () => entry.commit(to)
      )
    };
    const promise = entry.pendingLoad.then(() => {
      return entry.staged === _runtime.STAGED_NO_VALUE ? data.value : entry.staged;
    }).catch((e) => parentEntry ? Promise.reject(e) : null);
    _runtime.setCurrentContext.call(void 0, currentContext);
    return Object.assign(promise, useDataLoaderResult);
  };
  useDataLoader[_runtime.IS_USE_DATA_LOADER_KEY] = true;
  useDataLoader._ = {
    load,
    options,
    // @ts-expect-error: return type has the generics
    getEntry(router) {
      return router[_runtime.LOADER_ENTRIES_KEY].get(loader);
    }
  };
  return useDataLoader;
}
var DEFAULT_DEFINE_LOADER_OPTIONS = {
  lazy: false,
  server: true,
  commit: "after-load"
};
var SERVER_INITIAL_DATA_KEY = Symbol();
var INITIAL_DATA_KEY = Symbol();


exports.defineBasicLoader = defineBasicLoader;
