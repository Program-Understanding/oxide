<template>
    <div class="diff-box">
        <slot></slot>
    </div>
</template>

<script>
export default {
    name: 'Diff-Box'
}
</script>
<script></script>
<style scoped>
.diff-box {
    flex: 1;
    background-color: #272E33; /* Explicit background color */
    margin: 0.5rem;
    border: 1px solid #ffffff; /* Explicit border color */
    padding: 16px;
    border-radius: 4px;
}
</style>