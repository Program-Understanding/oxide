<script setup>
import { ref, watch } from "vue";
import { selectedModule, selectedCollection, responseData, collectionFiles } from "./state";
import ScrollPanel from "primevue/scrollpanel";
import Sidebar from './components/sidebar.vue';
const selectedFile = ref('');
const oid = ref('');

// Fetch modules and collections
const [modules, collections] = await Promise.all([
    fetch("http://localhost:8000/api/modules/").then((res) => res.json()),
    fetch("http://localhost:8000/api/collections/").then((res) => res.json()),
]);

// Watch for changes in collection
watch(selectedCollection, async (newVal) => {
    responseData.value = {};
    if (newVal) {
        try {
            const url = new URL("http://localhost:8000/api/collections/files");
            url.searchParams.append("selected_collection", newVal);

            const response = await fetch(url);
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            const data = await response.json();
            collectionFiles.value = data;


        } catch (error) {
            console.error(error);
            collectionFiles.value = [];
        }
    } else {
        collectionFiles.value = [];
    }
});

// Watch for changes in selectedFile
watch(selectedFile, async (newVal) => {
    responseData.value = {};
    if (newVal) {
        try {
            oid.value = collectionFiles.value[newVal.value];
            oid.value = oid.value.substring(1, oid.value.length);

            console.log(oid.value);

        } catch (error) {
            console.error(error);
        }
    }
});

// Function to run the module
const runModule = async () => {
    if (!selectedModule.value || !selectedCollection.value || !selectedFile.value) {
        return;
    }

    try {
        const url = new URL("http://localhost:8000/api/retrieve");
        url.searchParams.append("selected_module", selectedModule.value);
        url.searchParams.append("selected_collection", selectedCollection.value);

        const response = await fetch(url);
        if (!response.ok) {
            throw new Error(`HTTP error! status: ${response.status}`);
        }
        const data = await response.json();
        if (data[oid.value]) {
            responseData.value = data[oid.value];
        } else {
            responseData.value = data;
        }


        console.log('Module data:', data);
    } catch (error) {
        console.error(error);
    }
};


const handleFileSelection = (file) => {
    selectedFile.value = file;
};
</script>

<template>
    <div class="flex flex-col min-h-screen h-screen bg-zinc-900">
        <Sidebar @goToRoot="goToRoot"/>

        <div class="flex flex-row flex-grow pt-4">
            <div class="flex flex-row space-x-4" style="flex-grow: 0; flex-shrink: 0">
                <div class="card bg-primary w-1/2 flex flex-col pb-4 pl-4">
                    <div class="flex flex-grow min-h-0 pb-4 h-64">
                        <Listbox v-model="selectedCollection" :options="collections" filter scrollHeight="95%" />
                    </div>
                    <div class="flex flex-grow min-h-0 pb-4 h-64">
                        <Listbox v-model="selectedFile" :options="Object.keys(collectionFiles)" filter
                            scrollHeight="95%" @change="handleFileSelection" />
                    </div>
                </div>
                <div class="card w-1/2 flex flex-col pb-4">
                    <div class="flex flex-grow min-h-0 pb-4 h-64">
                        <Listbox v-model="selectedModule" :options="modules" filter scrollHeight="95%" />
                    </div>
                </div>
            </div>
            <div class="flex flex-col flex-grow">
                <div class="flex flex-row justify-between">
                    <div class="self-start mb-4 pl-4">
                        <Button :disabled="!selectedModule || !selectedCollection || !selectedFile" @click="runModule" class="btn">Run
                            module</Button>
                    </div>
                </div>
                <div class="flex items-center pl-4 pb-8 pr-4" style="height: 95vh; max-width: 100%; position: relative">
                    <div class="bg-gray-800 border border-gray-300 w-full h-full">
                        <ScrollPanel id="scrollpanel" style="width: 1250px; height: 100%; overflow: auto;">
                            <pre>{{ JSON.stringify(responseData, null, 2)}}</pre>
                            <div id="infoBox" class="info-box" v-if="selectedModule == 'binary_visualizer' && viewMode == 'chart'"></div>
                        </ScrollPanel>
                    </div>
                </div>
            </div>
        </div>
    </div>
</template>

<style>
@import url("~/assets/css/base.css");

.info-box {
    position: fixed;
    right: 5%;
    top: 50%;
    width: 300px;
    border: 1px solid black;
    padding: 10px;
    box-shadow: 0 0 10px rgba(0, 0, 0, 0.1);
    z-index: 1000;
}
</style>