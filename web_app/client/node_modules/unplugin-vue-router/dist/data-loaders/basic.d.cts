import { RouteMap, RouteLocationNormalizedLoaded } from 'vue-router';
import { DefineLoaderFn, DefineDataLoaderOptionsBase, DataLoaderContextBase, UseDataLoader } from 'unplugin-vue-router/runtime';

/**
 * Creates a data loader composable that can be exported by pages to attach the data loading to a route. This returns a
 * composable that can be used in any component.
 *
 * @experimental
 * Still under development and subject to change. See https://github.com/vuejs/rfcs/discussions/460
 *
 * @param name - name of the route to have typed routes
 * @param loader - function that returns a promise with the data
 * @param options - options to configure the data loader
 */
declare function defineBasicLoader<Name extends keyof RouteMap, Data, isLazy extends boolean>(name: Name, loader: DefineLoaderFn<Data, DataLoaderContext, RouteLocationNormalizedLoaded<Name>>, options?: DefineDataLoaderOptions<isLazy>): UseDataLoaderBasic<isLazy, Data>;
declare function defineBasicLoader<Data, isLazy extends boolean>(loader: DefineLoaderFn<Data, DataLoaderContext, RouteLocationNormalizedLoaded>, options?: DefineDataLoaderOptions<isLazy>): UseDataLoaderBasic<isLazy, Data>;
interface DefineDataLoaderOptions<isLazy extends boolean> extends DefineDataLoaderOptionsBase<isLazy> {
    /**
     * Key to use for SSR state. This will be used to read the initial data from `initialData`'s object.
     */
    key?: string;
}
interface DataLoaderContext extends DataLoaderContextBase {
}
/**
 * Symbol used to store the data in the router so it can be retrieved after the initial navigation.
 * @internal
 */
declare const SERVER_INITIAL_DATA_KEY: unique symbol;
/**
 * Initial data generated on server and consumed on client.
 * @internal
 */
declare const INITIAL_DATA_KEY: unique symbol;
declare module 'vue-router' {
    interface Router {
        /**
         * Gives access to the initial state during rendering. Should be set to `false` once it's consumed.
         * @internal
         */
        [SERVER_INITIAL_DATA_KEY]?: Record<string, unknown> | false;
        [INITIAL_DATA_KEY]?: Record<string, unknown> | false;
    }
}
interface UseDataLoaderBasic<isLazy extends boolean, Data> extends UseDataLoader<isLazy, Data> {
}

export { type DataLoaderContext, type DefineDataLoaderOptions, type UseDataLoaderBasic, defineBasicLoader };
