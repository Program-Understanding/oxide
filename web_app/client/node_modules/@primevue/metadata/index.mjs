// src/components/index.ts
var form = toMeta([
  "AutoComplete",
  "Calendar",
  "CascadeSelect",
  "Checkbox",
  "CheckboxGroup",
  "Chips",
  "ColorPicker",
  "DatePicker",
  "Dropdown",
  "Editor",
  "FloatLabel",
  "Fluid",
  "IconField",
  "IftaLabel",
  "InputChips",
  "InputGroup",
  "InputGroupAddon",
  "InputIcon",
  "InputMask",
  "InputNumber",
  "InputOtp",
  "InputSwitch",
  "InputText",
  "Knob",
  "Listbox",
  "MultiSelect",
  "Password",
  "RadioButton",
  "RadioButtonGroup",
  "Rating",
  "Select",
  "SelectButton",
  "Slider",
  "Textarea",
  "ToggleButton",
  "ToggleSwitch",
  "TreeSelect"
]);
var button = toMeta(["Button", "ButtonGroup", "SpeedDial", "SplitButton"]);
var data = toMeta(["Column", "Row", "ColumnGroup", "DataTable", "DataView", "OrderList", "OrganizationChart", "Paginator", "PickList", "Tree", "TreeTable", "Timeline", "VirtualScroller"]);
var panel = toMeta([
  "Accordion",
  "AccordionPanel",
  "AccordionHeader",
  "AccordionContent",
  "AccordionTab",
  "Card",
  "DeferredContent",
  "Divider",
  "Fieldset",
  "Panel",
  "ScrollPanel",
  "Splitter",
  "SplitterPanel",
  "Stepper",
  "StepList",
  "Step",
  "StepItem",
  "StepPanels",
  "StepPanel",
  "TabView",
  "Tabs",
  "TabList",
  "Tab",
  "TabPanels",
  "TabPanel",
  "Toolbar"
]);
var overlay = toMeta([
  { name: "ConfirmDialog", use: { as: "ConfirmationService" } },
  { name: "ConfirmPopup", use: { as: "ConfirmationService" } },
  "Dialog",
  "Drawer",
  { name: "DynamicDialog", use: { as: "DialogService" } },
  "OverlayPanel",
  "Popover",
  "Sidebar"
]);
var file = toMeta(["FileUpload"]);
var menu = toMeta(["Breadcrumb", "ContextMenu", "Dock", "Menu", "Menubar", "MegaMenu", "PanelMenu", "Steps", "TabMenu", "TieredMenu"]);
var chart = toMeta(["Chart"]);
var messages = toMeta(["Message", "InlineMessage", { name: "Toast", use: { as: "ToastService" } }]);
var media = toMeta(["Carousel", "Galleria", "Image", "ImageCompare"]);
var misc = toMeta(["Avatar", "AvatarGroup", "Badge", "BlockUI", "Chip", "Inplace", "MeterGroup", "OverlayBadge", "ScrollTop", "Skeleton", "ProgressBar", "ProgressSpinner", "Tag", "Terminal"]);
var extensions = toMeta([
  { name: "Form", from: "@primevue/forms/form" },
  { name: "FormField", from: "@primevue/forms/formfield" }
]);
var components = [...form, ...button, ...data, ...panel, ...overlay, ...file, ...menu, ...chart, ...messages, ...media, ...misc, ...extensions];

// src/composables/index.ts
var composables = toMeta([
  { name: "usePrimeVue", as: "usePrimeVue", from: "primevue/config" },
  { name: "useStyle", as: "useStyle", from: "primevue/usestyle" },
  { name: "useConfirm", as: "useConfirm", from: "primevue/useconfirm" },
  { name: "useToast", as: "useToast", from: "primevue/usetoast" },
  { name: "useDialog", as: "useDialog", from: "primevue/usedialog" }
]);

// src/directives/index.ts
var directives = toMeta([
  { name: "badge", as: "BadgeDirective", from: "primevue/badgedirective" },
  { name: "tooltip", as: "Tooltip", from: "primevue/tooltip" },
  { name: "ripple", as: "Ripple", from: "primevue/ripple" },
  { name: "styleclass", as: "StyleClass", from: "primevue/styleclass" },
  { name: "focustrap", as: "FocusTrap", from: "primevue/focustrap" },
  { name: "animateonscroll", as: "AnimateOnScroll", from: "primevue/animateonscroll" },
  { name: "keyfilter", as: "KeyFilter", from: "primevue/keyfilter" }
]);

// src/index.ts
function toMeta(arr) {
  return arr == null ? void 0 : arr.map((item) => {
    var _a;
    const it = typeof item === "string" ? { name: item } : item;
    it.as ??= it == null ? void 0 : it.name;
    it.from ??= `primevue/${(_a = it == null ? void 0 : it.name) == null ? void 0 : _a.toLowerCase()}`;
    return it;
  });
}
export {
  button,
  chart,
  components,
  composables,
  data,
  directives,
  extensions,
  file,
  form,
  media,
  menu,
  messages,
  misc,
  overlay,
  panel,
  toMeta
};
