export declare const reuniteConfigSchema: {
    readonly type: "object";
    readonly properties: {
        readonly ignoreLint: {
            readonly type: "boolean";
            readonly default: false;
        };
        readonly ignoreLinkChecker: {
            readonly type: "boolean";
        };
        readonly ignoreMarkdocErrors: {
            readonly type: "boolean";
        };
    };
    readonly additionalProperties: false;
};
