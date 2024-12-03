"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.ParametersNotInBody = void 0;
const ParametersNotInBody = () => {
    return {
        Parameter: {
            enter(parameter, { report, location }) {
                if (parameter.in === 'body') {
                    report({
                        message: 'The `body` value of the `in` property is not supported by Spot.',
                        location: location.child(['in']),
                    });
                }
            },
        },
    };
};
exports.ParametersNotInBody = ParametersNotInBody;
