"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.SourceDescriptionType = void 0;
const SourceDescriptionType = () => {
    return {
        SourceDescriptions: {
            enter(SourceDescriptions, { report, location }) {
                for (const sourceDescription of SourceDescriptions) {
                    if (!['openapi', 'arazzo'].includes(sourceDescription?.type)) {
                        report({
                            message: 'The `type` property of the `sourceDescription` object must be either `openapi` or `arazzo`.',
                            location: location.child([SourceDescriptions.indexOf(sourceDescription)]),
                        });
                    }
                }
            },
        },
    };
};
exports.SourceDescriptionType = SourceDescriptionType;
