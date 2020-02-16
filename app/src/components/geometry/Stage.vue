<template>
    <v-stage :config="configKonva">
        <v-layer>
           <Point :x=200 :y=300 :id="pointText"></Point>
        </v-layer>
    </v-stage>
</template>

<script>
const width = window.innerWidth
const height = window.innerHeight
import Point from "./Point"
export default {
    name: 'Stage',
    components: {
        Point
    },
    data() {
        return {
            configKonva: {
                width: width,
                height: height
            },
            pointText: "A",
        };
    }
};
</script>

<style scoped>

</style>