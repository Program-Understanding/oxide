<template>
    <div class="sidebar-container" @mouseover="showSidebar" @mouseleave="hideSidebar">
        <div class="sidebar-content" :class="{ 'sidebar-visible': isVisible }">
            <slot></slot>
            <button @click="goToRoot">Go to Root Page</button>
        </div>
    </div>
</template>

<script>
import { ref } from 'vue';

export default {
    name: 'Sidebar',
    emits: ['goToRoot'],
    setup(_, { emit }) {
        const isVisible = ref(false);

        const showSidebar = () => {
            isVisible.value = true;
        };

        const hideSidebar = () => {
            isVisible.value = false;
        };

        const goToRoot = () => {
            window.location.href = '/';
        };

        return {
            isVisible,
            showSidebar,
            hideSidebar,
            goToRoot,
        };
    },
};
</script>

<style scoped>
.sidebar-container {
    position: fixed;
    left: 0;
    top: 0;
    height: 100%;
    width: 10px;
    z-index: 1000;
}

.sidebar-content {
    width: 200px;
    height: 100%;
    background-color: #272E33;
    color: white;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    transform: translateX(-200px);
    transition: transform 0.3s;
    opacity: .7;
}

.sidebar-visible {
    transform: translateX(0);
}

button {
    margin: 10px 0;
    padding: 10px 20px;
    background-color: #444;
    color: white;
    border: none;
    cursor: pointer;
}

button:hover {
    background-color: #555;
}
</style>