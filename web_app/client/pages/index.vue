<script>
export default {
    data() {
        return {
            nav: [
                { label: 'Modules Visuals', to: '/oxide_visuals' },
                { label: 'Chart Views', to: '/chart_views' },
                { label: 'Disassembly Differences', to: '/diff_view' },
                { label: 'Binary Visual Map', to: '/binary_visualizer' },
            ]
        };
    }
};
</script>

<template>
<div class="flex items-center justify-center min-h-screen">
    <!-- Container for the cards -->
    <div class="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
        <!-- Each card is a router-link -->
        <router-link v-for="item in nav" :key="item.to" :to="item.to" class="bg-gray-800 shadow-md rounded-lg p-6 hover:bg-gray-700 hover:shadow-lg hover:shadow-blue-500/50 transition duration-300 flex flex-col no-underline">
            <!-- Card title -->
            <h2 class="text-xl font-bold mb-2 text-white flex-grow">{{ item.label }}</h2>
            <!-- Card description -->
            <p class="text-gray-400 mb-4 flex-grow">Short description for {{ item.label }}</p>
        </router-link>
    </div>
</div>
</template>

<style scoped>
.grid > router-link {
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    text-decoration: none;
    height: 100%; /* Ensure all cards have the same height */
}
</style>