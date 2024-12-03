import { MetaType } from '@primevue/metadata';
import { ComponentResolveResult, ComponentResolver } from 'unplugin-vue-components/types';

interface PrimeVueResolverOptions {
    components?: {
        prefix?: string;
    };
    directives?: {
        prefix?: string;
    };
    resolve?: (meta: MetaType, type: string) => ComponentResolveResult;
}
declare function PrimeVueResolver(options?: PrimeVueResolverOptions): ComponentResolver[];

export { PrimeVueResolver, type PrimeVueResolverOptions };
