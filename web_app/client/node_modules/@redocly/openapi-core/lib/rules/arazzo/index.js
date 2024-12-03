"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.preprocessors = exports.rules = void 0;
const spec_1 = require("../common/spec");
const assertions_1 = require("../common/assertions");
const parameters_not_in_body_1 = require("../spot/parameters-not-in-body");
const source_description_type_1 = require("../arazzo/source-description-type");
const version_enum_1 = require("../spot/version-enum");
const workflowId_unique_1 = require("./workflowId-unique");
const stepId_unique_1 = require("./stepId-unique");
const sourceDescriptions_name_unique_1 = require("./sourceDescriptions-name-unique");
const workflow_dependsOn_1 = require("./workflow-dependsOn");
const parameters_unique_1 = require("./parameters-unique");
const step_onSuccess_unique_1 = require("./step-onSuccess-unique");
const step_onFailure_unique_1 = require("./step-onFailure-unique");
const requestBody_replacements_unique_1 = require("./requestBody-replacements-unique");
const no_criteria_xpath_1 = require("../spot/no-criteria-xpath");
const no_actions_type_end_1 = require("../spot/no-actions-type-end");
const criteria_unique_1 = require("./criteria-unique");
exports.rules = {
    spec: spec_1.Spec,
    assertions: assertions_1.Assertions,
    'parameters-not-in-body': parameters_not_in_body_1.ParametersNotInBody,
    'sourceDescription-type': source_description_type_1.SourceDescriptionType,
    'version-enum': version_enum_1.VersionEnum,
    'workflowId-unique': workflowId_unique_1.WorkflowIdUnique,
    'stepId-unique': stepId_unique_1.StepIdUnique,
    'sourceDescription-name-unique': sourceDescriptions_name_unique_1.SourceDescriptionsNameUnique,
    'workflow-dependsOn': workflow_dependsOn_1.WorkflowDependsOn,
    'parameters-unique': parameters_unique_1.ParametersUnique,
    'step-onSuccess-unique': step_onSuccess_unique_1.StepOnSuccessUnique,
    'step-onFailure-unique': step_onFailure_unique_1.StepOnFailureUnique,
    'requestBody-replacements-unique': requestBody_replacements_unique_1.RequestBodyReplacementsUnique,
    'no-criteria-xpath': no_criteria_xpath_1.NoCriteriaXpath,
    'no-actions-type-end': no_actions_type_end_1.NoActionsTypeEnd,
    'criteria-unique': criteria_unique_1.CriteriaUnique,
};
exports.preprocessors = {};
