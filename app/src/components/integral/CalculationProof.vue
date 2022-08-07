<template>
  <div>
    <span class="math-text">by calculation</span>
    <span v-if="item.finished" class="math-text" style="color: green">&nbsp;(finished)</span><br/>
    <span class="math-text">{{label}}1.</span>&nbsp;
    <span class="math-text">LHS: </span>
    <Calculation v-bind:item="item.lhs_calc" v-bind:label="label + '1.'"
                 v-bind:selected_item="selected_item"
                 v-bind:selected_facts="selected_facts"
                 @select="(lbl) => $emit('select', lbl)"/>
    <span class="math-text">{{label}}2.</span>&nbsp;
    <span class="math-text">RHS: </span>
    <Calculation v-bind:item="item.rhs_calc" v-bind:label="label + '2.'"
                 v-bind:selected_item="selected_item"
                 v-bind:selected_facts="selected_facts"
                 @select="(lbl) => $emit('select', lbl)"/>
  </div>
</template>

<script>
import Calculation from './Calculation.vue'

export default {
  name: "CalculationProof",
  components: {
    Calculation,
  },

  props: [
    "item",
    "label",
    "selected_item",
    "selected_facts",
  ]
}

</script>
