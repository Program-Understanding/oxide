<template>
    <div class="chartpopup" v-if="showPopup">
        <div class="popup-content">
            <h1>Select Chart Type and File</h1>
            <div v-if="step === 1">
                <label for="chartType" style="font-size: 23px; font-weight: bold;">Chart Type:</label>
                <select v-model="selectedChartType" class="styled-select">
                    <option v-for="module in chartModules" :key="module" :value="module">{{ module }}</option>
                </select>
                <div class="buttons">
                    <button @click="nextStep">Next</button>
                </div>
            </div>
            <div v-if="step === 2">
                <label for="collection" style="font-size: 23px; font-weight: bold;">Collection:</label>
                <select v-model="selectedCollection" class="styled-select">
                    <option v-for="collection in collections" :key="collection" :value="collection">{{ collection }}</option>
                </select>
                <div class="buttons">
                    <button @click="previousStep">Back</button>
                    <button id="nextButton" @click="nextStep">Next</button>
                </div>
            </div>
            <div v-if="step === 3">
                <label for="file" style="font-size: 23px; font-weight: bold;">File:</label>
                <select v-model="selectedFile" class="styled-select">
                    <option v-for="file in collectionFiles" :key="file" :value="file">{{ file }}</option>
                </select>
                <div class="buttons">
                    <button @click="previousStep">Back</button>
                    <button @click="confirmSelection">Confirm</button>
                </div>
            </div>
        </div>
    </div>
</template>

<script>
import { ref, watch, onMounted } from 'vue';

export default {
    name: 'ChartPopup',
    props: {
        chartModules: Array,
        collections: Array,
    },
    setup(props, { emit }) {
        const showPopup = ref(true);
        const step = ref(1);
        const selectedChartType = ref(props.chartModules[0]);
        const selectedCollection = ref(props.collections[0]);
        const collectionFiles = ref([]);
        const collectionFilesOG = ref([]);
        const selectedFile = ref('');
        const selectedFileOG = ref('');
        const oid = ref('');
        const data = ref({});

        const loadCollectionFiles = async (collection) => {
            try {
                const url = new URL("http://localhost:8000/api/collections/files");
                url.searchParams.append("selected_collection", collection);

                const response = await fetch(url);
                if (!response.ok) {
                    throw new Error(`HTTP error! status: ${response.status}`);
                }
                data.value = await response.json();

                collectionFiles.value = Object.keys(data.value).map(key => key.replace(/[{}']/g, ''));
                selectedFile.value = collectionFiles.value[0];

                collectionFilesOG.value = Object.keys(data.value);
                selectedFileOG.value = collectionFilesOG.value[0];

                oid.value = data.value[selectedFileOG.value];
                oid.value = oid.value.substring(1, oid.value.length);

            } catch (error) {
                console.error(error);
                collectionFiles.value = [];
            }
        };

        watch(selectedCollection, (newVal) => {
            if (newVal) {
                loadCollectionFiles(newVal);
            }
        });

        watch(selectedFile, (newVal) => {
            if (newVal) {
                selectedFile.value = newVal;
                
                let fileName = `{'${newVal}'}`;

                oid.value = data.value[fileName];
                oid.value = oid.value.substring(1, oid.value.length);
            }
        });

        onMounted(() => {
            loadCollectionFiles(selectedCollection.value);
        });

        const nextStep = () => {
            if (step.value < 3) {
                step.value++;
            }
        };

        const previousStep = () => {
            if (step.value > 1) {
                step.value--;
            }
        };

        const confirmSelection = () => {
            emit('selectionConfirmed', {
                chartType: selectedChartType.value,
                collection: selectedCollection.value,
                file: selectedFile.value,
                oid: oid.value,
            });
            showPopup.value = false;
        };

        return {
            showPopup,
            step,
            selectedChartType,
            selectedCollection,
            collectionFiles,
            selectedFile,
            oid,
            nextStep,
            previousStep,
            confirmSelection,
        };
    },
};
</script>

<style scoped>
.chartpopup {
    position: fixed;
    top: 0;
    left: 0;
    width: 100%;
    height: 100%;
    background-color: #272E33;
    display: flex;
    justify-content: center;
    align-items: center;
}

.popup-content {
    background: white;
    padding: 20px;
    width: 600px;
    height: 400px;
    border-radius: 8px;
    text-align: center;
    color: black; /* Ensure text color is black */
}

.styled-select {
    width: 100%;
    height: 50px;
    font-size: larger;
    padding: 10px;
    margin: 10px 0;
    border: 1px solid #ccc;
    border-radius: 4px;
    background-color: #f0f0f0; /* Background color */
    color: #333; /* Text color */
    font-weight: bold;
}

.styled-select option {
    background-color: #f0f0f0; /* Background color for options */
    color: #333; /* Text color for options */
    font-size: larger;
}

.buttons {
    margin-top: 20px;
    
}

button {
    margin: 0 10px;
    border-radius: 5px;
    border: 2px solid #272E33;;
    padding: 5px;
    width: 100px;
    height: 50px;
    font-size: large;
    font-weight: bold;
}

h1 {
    font-size: x-large;
    color: #272E33;

    margin-bottom: 50px;
    border-radius: 5px;
    border: 2px solid #272E33;;

}
</style>