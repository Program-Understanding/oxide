import type { BuiltInAsync2RuleId, BuiltInAsync3RuleId, BuiltInCommonOASRuleId, BuiltInArazzoRuleId, BuiltInOAS2RuleId, BuiltInOAS3RuleId } from './types/redocly-yaml';
import type { Oas3Rule, Oas3Preprocessor, Oas2Rule, Oas2Preprocessor, Async2Preprocessor, Async2Rule, Async3Preprocessor, Async3Rule, ArazzoPreprocessor, ArazzoRule } from './visitors';
export declare enum SpecVersion {
    OAS2 = "oas2",
    OAS3_0 = "oas3_0",
    OAS3_1 = "oas3_1",
    Async2 = "async2",
    Async3 = "async3",
    Arazzo = "arazzo"
}
export declare enum SpecMajorVersion {
    OAS2 = "oas2",
    OAS3 = "oas3",
    Async2 = "async2",
    Async3 = "async3",
    Arazzo = "arazzo"
}
export type RuleMap<Key extends string, RuleConfig, T> = Record<T extends 'built-in' ? Key : string, RuleConfig>;
export type Oas3RuleSet<T = undefined> = RuleMap<BuiltInCommonOASRuleId | BuiltInOAS3RuleId | 'assertions', Oas3Rule, T>;
export type Oas2RuleSet<T = undefined> = RuleMap<BuiltInCommonOASRuleId | BuiltInOAS2RuleId | 'assertions', Oas2Rule, T>;
export type Async2RuleSet<T = undefined> = RuleMap<BuiltInAsync2RuleId | 'assertions', Async2Rule, T>;
export type Async3RuleSet<T = undefined> = RuleMap<BuiltInAsync3RuleId | 'assertions', Async3Rule, T>;
export type ArazzoRuleSet<T = undefined> = RuleMap<BuiltInArazzoRuleId | 'assertions', ArazzoRule, T>;
export type Oas3PreprocessorsSet = Record<string, Oas3Preprocessor>;
export type Oas2PreprocessorsSet = Record<string, Oas2Preprocessor>;
export type Async2PreprocessorsSet = Record<string, Async2Preprocessor>;
export type Async3PreprocessorsSet = Record<string, Async3Preprocessor>;
export type ArazzoPreprocessorsSet = Record<string, ArazzoPreprocessor>;
export type Oas3DecoratorsSet = Record<string, Oas3Preprocessor>;
export type Oas2DecoratorsSet = Record<string, Oas2Preprocessor>;
export type Async2DecoratorsSet = Record<string, Async2Preprocessor>;
export type Async3DecoratorsSet = Record<string, Async3Preprocessor>;
export type ArazzoDecoratorsSet = Record<string, ArazzoPreprocessor>;
export declare function detectSpec(root: unknown): SpecVersion;
export declare function getMajorSpecVersion(version: SpecVersion): SpecMajorVersion;
export declare function getTypes(spec: SpecVersion): Record<string, import("./types").NodeType> | Record<"Root" | "Tag" | "TagList" | "ExternalDocs" | "SecurityRequirement" | "SecurityRequirementList" | "Info" | "Contact" | "License" | "Paths" | "PathItem" | "Parameter" | "ParameterList" | "ParameterItems" | "Operation" | "Example" | "ExamplesMap" | "Examples" | "Header" | "Responses" | "Response" | "Schema" | "Xml" | "SchemaProperties" | "NamedSchemas" | "NamedResponses" | "NamedParameters" | "NamedSecuritySchemes" | "SecurityScheme" | "TagGroup" | "TagGroups" | "EnumDescriptions" | "Logo" | "XCodeSample" | "XCodeSampleList" | "XServer" | "XServerList", import("./types").NodeType> | Record<"Root" | "Tag" | "TagList" | "ExternalDocs" | "SecurityRequirement" | "SecurityRequirementList" | "Info" | "Contact" | "License" | "Paths" | "PathItem" | "Parameter" | "ParameterList" | "Operation" | "Example" | "ExamplesMap" | "Header" | "Responses" | "Response" | "Schema" | "Xml" | "SchemaProperties" | "NamedSchemas" | "NamedResponses" | "NamedParameters" | "NamedSecuritySchemes" | "SecurityScheme" | "TagGroup" | "TagGroups" | "EnumDescriptions" | "Logo" | "XCodeSample" | "XCodeSampleList" | "Server" | "ServerList" | "ServerVariable" | "ServerVariablesMap" | "Callback" | "CallbacksMap" | "RequestBody" | "MediaTypesMap" | "MediaType" | "Encoding" | "EncodingMap" | "HeadersMap" | "Link" | "LinksMap" | "DiscriminatorMapping" | "Discriminator" | "Components" | "NamedExamples" | "NamedRequestBodies" | "NamedHeaders" | "NamedLinks" | "NamedCallbacks" | "ImplicitFlow" | "PasswordFlow" | "ClientCredentials" | "AuthorizationCode" | "OAuth2Flows" | "XUsePkce" | "WebhooksMap", import("./types").NodeType> | Record<"Root" | "Info" | "License" | "Operation" | "Schema" | "SchemaProperties" | "SecurityScheme" | "Components" | "PatternProperties" | "NamedPathItems" | "DependentRequired", import("./types").NodeType>;
