type TarFileItem<DataT = Uint8Array> = {
    /**
     * File name
     */
    name: string;
    /**
     * File data (don't provide for directories)
     */
    data?: DataT;
    /**
     * File attributes
     */
    attrs?: TarFileAttrs;
};
interface ParsedTarFileItem extends TarFileItem {
    type: "file" | "directory" | number;
    size: number;
    readonly text: string;
}
interface TarFileAttrs {
    /**
     * Default: 664 (-rw-rw-r--) for files and 775 (-rwxrwxr-x) for directories and  */
    mode?: string;
    /**
     * Default: 1000
     */
    uid?: number;
    /**
     * Default: 1000
     */
    gid?: number;
    /**
     * Default: Date.now()
     */
    mtime?: number;
    /**
     * Default: ""
     */
    user?: string;
    /**
     * Default: ""
     */
    group?: string;
}

declare function parseTar(data: ArrayBuffer | Uint8Array): TarFileItem[];
declare function parseTarGzip(data: ArrayBuffer | Uint8Array, opts?: {
    compression?: CompressionFormat;
}): Promise<TarFileItem[]>;

interface CreateTarOptions {
    attrs?: TarFileAttrs;
}
type TarFileInput = TarFileItem<string | Uint8Array | ArrayBuffer>;
declare function createTar(files: TarFileInput[], opts?: CreateTarOptions): Uint8Array;
declare function createTarGzipStream(files: TarFileInput[], opts?: CreateTarOptions & {
    compression?: CompressionFormat;
}): ReadableStream;
declare function createTarGzip(files: TarFileInput[], opts?: CreateTarOptions & {
    compression?: CompressionFormat;
}): Promise<Uint8Array>;

export { type CreateTarOptions, type ParsedTarFileItem, type TarFileAttrs, type TarFileInput, type TarFileItem, createTar, createTarGzip, createTarGzipStream, parseTar, parseTarGzip };
