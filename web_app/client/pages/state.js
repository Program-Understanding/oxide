import { ref } from "vue";

export const selectedModule = ref();
export const selectedCollection = ref();
export const chartInstance = ref(null);
export const responseData = ref(null);
export const tableData = ref([]);
export const collectionFiles = ref([]);
export let showTable = ref();