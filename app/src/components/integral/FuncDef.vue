<template>
  <div class="indented-label">
    <span class="math-text">{{label}}.</span>&nbsp;
    <div>
      <span class="math-text">Introduce definition</span>
      <div @click="$emit('select', label)"
           :class="{selected: selected_item === label}">
        <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" class="indented-text"/>
      </div>
    </div>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "FuncDef",
  components: {
    MathEquation
  },

  props: [
    "item",
    "label",
    "selected_item",
  ],

  emits: [
    "select"
  ],
}

</script>
