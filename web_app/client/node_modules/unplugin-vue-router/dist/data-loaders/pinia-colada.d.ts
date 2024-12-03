import { RouteMap, RouteLocationNormalizedLoaded, LocationQuery } from 'vue-router';
import { DefineDataLoaderOptionsBase, DefineLoaderFn, DataLoaderContextBase, UseDataLoaderResult, UseDataLoader, _PromiseMerged, NavigationResult, DataLoaderEntryBase } from 'unplugin-vue-router/runtime';
import { ShallowRef } from 'vue';
import { UseQueryOptions, EntryKey, UseQueryReturn } from '@pinia/colada';

/**
 * Creates a data loader composable that can be exported by pages to attach the data loading to a route. This returns a
 * composable that can be used in any component.
 *
 * The returned composable exposes a mix of Data Loaders state and Pinia
 * Colada state.
 * - `data`, `isLoading`, `error` are navigation dependent and follow data loaders behavior.
 * - `status`, `asyncStatus`, `state` are Pinia Colada state and will immediately change and reflect the state of the
 *   query.
 *
 * @experimental
 * Still under development and subject to change. See https://github.com/vuejs/rfcs/discussions/460
 *
 * @param name - name of the route to have typed routes
 * @param loader - function that returns a promise with the data
 * @param options - options to configure the data loader
 */
declare function defineColadaLoader<Name extends keyof RouteMap, Data, isLazy extends boolean>(name: Name, options: DefineDataColadaLoaderOptions<isLazy, Name, Data>): UseDataLoaderColada<isLazy, Data>;
declare function defineColadaLoader<Data, isLazy extends boolean>(options: DefineDataColadaLoaderOptions<isLazy, keyof RouteMap, Data>): UseDataLoaderColada<isLazy, Data>;
interface DefineDataColadaLoaderOptions<isLazy extends boolean, Name extends keyof RouteMap, Data> extends DefineDataLoaderOptionsBase<isLazy>, Omit<UseQueryOptions<unknown>, 'query' | 'key'> {
    /**
     * Key associated with the data and passed to pinia colada
     * @param to - Route to load the data
     */
    key: EntryKey | ((to: RouteLocationNormalizedLoaded<Name>) => EntryKey);
    /**
     * Function that returns a promise with the data.
     */
    query: DefineLoaderFn<Data, DataColadaLoaderContext, RouteLocationNormalizedLoaded<Name>>;
}
/**
 * @internal
 */
interface DataColadaLoaderContext extends DataLoaderContextBase {
}
interface UseDataLoaderColadaResult<isLazy extends boolean, Data> extends UseDataLoaderResult<isLazy, Data>, Pick<UseQueryReturn<Data, any>, 'isPending' | 'refetch' | 'refresh' | 'status' | 'asyncStatus' | 'state'> {
}
/**
 * Data Loader composable returned by `defineColadaLoader()`.
 */
interface UseDataLoaderColada<isLazy extends boolean, Data> extends UseDataLoader<isLazy, Data> {
    /**
     * Data Loader composable returned by `defineColadaLoader()`.
     *
     * @example
     * Returns the Data loader data, isLoading, error etc. Meant to be used in `setup()` or `<script setup>` **without `await`**:
     * ```vue
     * <script setup>
     * const { data, isLoading, error } = useUserData()
     * </script>
     * ```
     *
     * @example
     * It also returns a promise of the data when used in nested loaders. Note this `data` is **not a ref**. This is not meant to be used in `setup()` or `<script setup>`.
     * ```ts
     * export const useUserConnections = defineLoader(async () => {
     *   const user = await useUserData()
     *   return fetchUserConnections(user.id)
     * })
     * ```
     */
    (): _PromiseMerged<Exclude<Data, NavigationResult>, UseDataLoaderColadaResult<isLazy, Exclude<Data, NavigationResult>>>;
}
interface DataLoaderColadaEntry<isLazy extends boolean, Data> extends DataLoaderEntryBase<isLazy, Data> {
    /**
     * Reactive route passed to pinia colada so it automatically refetch
     */
    route: ShallowRef<RouteLocationNormalizedLoaded>;
    /**
     * Tracked routes to know when the data should be refreshed. Key is the key of the query.
     */
    tracked: Map<string, TrackedRoute>;
    /**
     * Extended options for pinia colada
     */
    ext: UseQueryReturn<Data> | null;
}
interface TrackedRoute {
    ready: boolean;
    params: Partial<LocationQuery>;
    query: Partial<LocationQuery>;
    hash: {
        v: string | null;
    };
}

export { type DataColadaLoaderContext, type DataLoaderColadaEntry, type DefineDataColadaLoaderOptions, type UseDataLoaderColada, type UseDataLoaderColadaResult, defineColadaLoader };
