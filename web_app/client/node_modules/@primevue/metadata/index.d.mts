declare const form: MetaType[];
declare const button: MetaType[];
declare const data: MetaType[];
declare const panel: MetaType[];
declare const overlay: MetaType[];
declare const file: MetaType[];
declare const menu: MetaType[];
declare const chart: MetaType[];
declare const messages: MetaType[];
declare const media: MetaType[];
declare const misc: MetaType[];
declare const extensions: MetaType[];
declare const components: MetaType[];

declare const composables: MetaType[];

declare const directives: MetaType[];

interface MetaType {
    name?: string;
    as?: string;
    from?: string;
    use?: {
        as?: string;
    };
}
declare function toMeta(arr?: any[]): MetaType[] | undefined;

export { type MetaType, button, chart, components, composables, data, directives, extensions, file, form, media, menu, messages, misc, overlay, panel, toMeta };
