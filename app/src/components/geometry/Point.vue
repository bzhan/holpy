<template>
    <v-group>
        <v-circle :config="configCircle"></v-circle>
        <v-text :config="configText"></v-text>
    </v-group>
</template>

<script>
    export default {
        name: "Point",
        data: function () {
            return {
                configCircle: {
                    x: this.x,
                    y: this.y,
                    radius: 5,
                    fill: this.fill,
                    stroke: "black",
                    strokeWidth: 2,
                },
            }
        },
        props: {
            x: {
                type: Number,
                default: 100
            },
            y: {
                type: Number,
                default: 100
            },
            id: {
                type: String,
                default: "undefined"
            },
            textCorner: {
                type: String,
                default: "upRight"
            },
            fill: {
                type: String,
                default: "red"
            }
        },
        computed: {
            configText: function () {
                return {
                    x: this.x,
                    y: this.y,
                    offsetX: -10,
                    offsetY: 20,
                    text: this.id,
                    fontSize: 20,
                }
            }
        }

    }
</script>

<style scoped>

</style>