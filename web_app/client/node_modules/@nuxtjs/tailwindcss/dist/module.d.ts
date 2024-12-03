import * as _nuxt_schema from '@nuxt/schema';
import resolveConfig from 'tailwindcss/resolveConfig.js';
import * as tailwindcss from 'tailwindcss';

type TWConfig = tailwindcss.Config;
type Arrayable<T> = T | Array<T>;
type InjectPosition = 'first' | 'last' | number | {
    after: string;
};
interface ExtendTailwindConfig {
    content?: TWConfig['content'] | ((contentDefaults: Array<string>) => TWConfig['content']);
}
interface ModuleOptions {
    /**
     * The path of the Tailwind configuration file. The extension can be omitted, in which case it will try to find a `.js`, `.cjs`, `.mjs`, or `.ts` file.
     *
     * @default 'tailwind.config'
     */
    configPath: Arrayable<string>;
    /**
     * The path of the Tailwind CSS file. If the file does not exist, the module's default CSS file will be imported instead.
     *
     * @default '~/assets/css/tailwind.css'
     */
    cssPath: string | false;
    /**
     * Configuration for Tailwind CSS
     *
     * for default, see https://tailwindcss.nuxtjs.org/tailwind/config
     */
    config: Omit<TWConfig, keyof ExtendTailwindConfig> & ExtendTailwindConfig;
    /**
     * [tailwind-config-viewer](https://github.com/rogden/tailwind-config-viewer) usage *in development*
     *
     * @default true
     */
    viewer: boolean;
    /**
     * Usage of configuration references in runtime. See https://tailwindcss.nuxtjs.org/tailwind/config#referencing-in-the-application
     *
     * @default false
     */
    exposeConfig: boolean;
    /**
     * Deeper references within configuration for optimal tree-shaking.
     *
     * @default 2
     */
    exposeLevel: number;
    /**
     * The position of CSS injection affecting CSS priority
     *
     * @default 'first'
     */
    injectPosition: InjectPosition;
    /**
     * @default false
     */
    disableHmrHotfix: boolean;
}

declare const _default: _nuxt_schema.NuxtModule<ModuleOptions>;

declare module '@nuxt/schema' {
    interface NuxtHooks {
        'tailwindcss:config': (tailwindConfig: Partial<TWConfig>) => void;
        'tailwindcss:loadConfig': (tailwindConfig: Partial<TWConfig> | undefined, configPath: string, index: number, configPaths: string[]) => void;
        'tailwindcss:resolvedConfig': (tailwindConfig: ReturnType<typeof resolveConfig<TWConfig>>) => void;
    }
}

export { ModuleOptions, _default as default };
