<template>
    <v-stage :config="configKonva">
        <v-layer>
            <v-circle :config="configCircle"></v-circle>
        </v-layer>
    </v-stage>
</template>

<script>
export default {
    name: 'Stage',
    data() {
        return {
            configKonva: {
                width: 200,
                height: 200
            },
            configCircle: {
                x: 100,
                y: 100,
                radius: 70,
                fill: "red",
                stroke: "black",
                strokeWidth: 4
            }
        };
    }
};
</script>

<style scoped>

</style>