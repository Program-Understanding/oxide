import * as _nuxt_schema from '@nuxt/schema';
import { PrimeVueConfiguration } from 'primevue/config';

interface ConstructsType {
    prefix?: string | undefined;
    name?: (item: any) => string | undefined;
    include?: '*' | Array<string | { name: string; use?: { as: string } }> | ((list: any) => string[] | undefined) | undefined;
    exclude?: '*' | Array<string | { name: string; use?: { as: string } }> | ((list: any) => string[] | undefined) | undefined;
}

interface ModuleOptions {
    usePrimeVue?: boolean;
    autoImport?: boolean;
    resolvePath?: any;
    /*cssLayerOrder?: string;*/
    importPT?: ImportOptions;
    importTheme?: ImportOptions;
    loadStyles?: boolean;
    options?: PrimeVueOptions;
    components?: ConstructsType;
    directives?: ConstructsType;
    composables?: Omit<ConstructsType, 'prefix'>;
}

interface PrimeVueOptions extends PrimeVueConfiguration {}

interface ImportOptions {
    as?: string;
    from: string;
}

declare module '@nuxt/schema' {
    interface NuxtConfig {
        primevue?: ModuleOptions;
    }
    interface NuxtOptions {
        primevue?: ModuleOptions;
    }
}

declare const _default: _nuxt_schema.NuxtModule<ModuleOptions, ModuleOptions, false>;

export { _default as default };
