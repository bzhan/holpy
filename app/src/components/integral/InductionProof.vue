<template>
  <div>
    <span class="math-text">{{label}}.</span>&nbsp;
    <span class="math-text">Show by induction on </span>
    <MathEquation v-bind:data="'\\(' + item.induct_var + '\\)'"/><br/>
    <span class="math-text">{{label}}.1. Base case</span><br>
    <CalculationProof v-bind:item="item.base_case" v-bind:label="label + '.1'"/>
    <span class="math-text">{{label}}.2. Induction case</span><br>
    <CalculationProof v-bind:item="item.induct_case" v-bind:label="label + '.2'"/>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'

export default {
  name: "InductionProof",
  components: {
    MathEquation,
    CalculationProof,
  },

  props: [
    "item",
    "label"
  ]
}

</script>
