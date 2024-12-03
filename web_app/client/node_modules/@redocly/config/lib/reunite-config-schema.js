"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.reuniteConfigSchema = void 0;
exports.reuniteConfigSchema = {
    type: 'object',
    properties: {
        ignoreLint: { type: 'boolean', default: false },
        ignoreLinkChecker: { type: 'boolean' },
        ignoreMarkdocErrors: { type: 'boolean' },
    },
    additionalProperties: false,
};
//# sourceMappingURL=reunite-config-schema.js.map