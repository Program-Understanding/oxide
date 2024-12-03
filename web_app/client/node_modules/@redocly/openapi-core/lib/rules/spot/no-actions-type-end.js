"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.NoActionsTypeEnd = void 0;
const NoActionsTypeEnd = () => {
    return {
        FailureActionObject: {
            enter(action, { report, location }) {
                if (action.type === 'end') {
                    report({
                        message: 'The `end` type action is not supported by Spot.',
                        location: location.child(['type']),
                    });
                }
            },
        },
        SuccessActionObject: {
            enter(action, { report, location }) {
                if (action.type === 'end') {
                    report({
                        message: 'The `end` type action is not supported by Spot.',
                        location: location.child(['type']),
                    });
                }
            },
        },
    };
};
exports.NoActionsTypeEnd = NoActionsTypeEnd;
