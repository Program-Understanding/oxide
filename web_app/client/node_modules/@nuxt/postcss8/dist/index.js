'use strict';

const path = require('path');
const semver = require('semver');
const defu = require('defu');

function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

const defu__default = /*#__PURE__*/_interopDefaultLegacy(defu);

var name = "@nuxt/postcss8";
var version = "1.1.3";

function postcss8Module() {
  const {nuxt} = this;
  const nuxtVersion = (nuxt.constructor.version || "0.0.0").split("-")[0];
  const expectedVersion = ">=2.15.3";
  if (!semver.satisfies(nuxtVersion, expectedVersion)) {
    throw new Error(`postcss@8 is not compatible with current version of nuxt (${nuxtVersion}). Expected: ${expectedVersion}`);
  }
  const moveToLast = (arr, item) => {
    if (!arr.includes(item)) {
      return arr;
    }
    return arr.filter((el) => el !== item).concat(item);
  };
  const moveToFirst = (arr, item) => {
    if (!arr.includes(item)) {
      return arr;
    }
    return [item].concat(arr.filter((el) => el !== item));
  };
  nuxt.options.build.postcss = defu__default['default'](nuxt.options.build.postcss, {
    plugins: {
      autoprefixer: {}
    },
    order(names) {
      names = moveToFirst(names, "postcss-url");
      names = moveToFirst(names, "postcss-import");
      names = moveToLast(names, "autoprefixer");
      return names;
    }
  });
  const pkgDir = path.resolve(__dirname, "..");
  global.__NUXT_PATHS__ = (global.__NUXT_PATHS__ || []).concat(pkgDir);
  global.__NUXT_PREPATHS__ = (global.__NUXT_PREPATHS__ || []).concat(pkgDir);
}
postcss8Module.meta = {
  name,
  version
};

module.exports = postcss8Module;
