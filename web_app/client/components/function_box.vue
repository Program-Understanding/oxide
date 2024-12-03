<template>
    <div class="functionbox">
        <slot></slot>
    </div>
</template>

<script>
export default {
    name: 'FunctionBox'
}
</script>

<style scoped>
.functionbox {
    flex:1;
    background-color: #272E33; /* Explicit background color */
    margin: 0.5rem;
    border: 1px solid #ffffff; /* Explicit border color */
    padding: 16px;
    border-radius: 4px;
}
</style>