<template>
  <div class="indented-label">
    <span class="math-text">{{label}}.</span>&nbsp;
    <div>
      <span class="math-text">Introduce definition</span>
      <div @click.exact="$emit('select', label)"
           @click.ctrl="$emit('select_fact', label)"
           :class="{selected: selected_item === label,
                    'selected-fact': label in selected_facts}">
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
    "selected_facts",
  ],

  emits: [
    "select",
    "select_fact"
  ],
}

</script>
