<template>
  <div class="indented-label">
    <span class="math-text">{{label}}</span>&nbsp;
    <div>
      <span class="math-text">Introduce definition</span>
      <div @click.exact="$emit('select', label)"
           @click.ctrl="$emit('select_fact', label)"
           :class="{selected: selected_item === label,
                    'selected-fact': label in selected_facts}">
        <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" class="indented-text"/>
        <span v-if="'conds' in item && item.conds.length > 0">
          <span class="math-text indented-text">for </span>
          <span v-for="(cond, index) in item.conds" :key="index">
            <span v-if="index > 0">, </span>
            <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
        </span>
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
