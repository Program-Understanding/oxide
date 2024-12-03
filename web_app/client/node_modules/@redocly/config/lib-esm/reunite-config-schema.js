export const reuniteConfigSchema = {
    type: 'object',
    properties: {
        ignoreLint: { type: 'boolean', default: false },
        ignoreLinkChecker: { type: 'boolean' },
        ignoreMarkdocErrors: { type: 'boolean' },
    },
    additionalProperties: false,
};
//# sourceMappingURL=reunite-config-schema.js.map