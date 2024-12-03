<template>
        <div class ="diff-container">
            <div class="header">
                <DiffHeader>Diff Header</DiffHeader>
            </div>
            <div class="content">
                <FunctionBox>First</FunctionBox>
                <DiffBox>First</DiffBox>
                <DiffBox>Second</DiffBox>
            </div>
        </div>   
</template>

<script>
import FunctionBox from './components/function_box.vue';
import DiffBox from './components/diff_box.vue';
import DiffHeader from './components/diff_header.vue';
export default {
    name: 'DiffView',
    components: {
        FunctionBox,
        DiffBox,
        DiffHeader,
    }
}
</script>

<style>
.content {
    display: flex;
    flex-direction: column;
}

</style>