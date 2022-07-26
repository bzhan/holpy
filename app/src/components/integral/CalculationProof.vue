<template>
  <div>
    <span class="math-text">{{label}}.</span>&nbsp;
    <span class="math-text">Show by calculation</span><br/>
    <span class="math-text">{{label}}.1.</span>&nbsp;
    <span class="math-text">LHS</span><br>
    <Calculation v-bind:steps="item.lhs_calc.steps"/>
    <span class="math-text">{{label}}.2.</span>&nbsp;
    <span class="math-text">RHS</span><br>
    <Calculation v-bind:steps="item.rhs_calc.steps"/>
  </div>
</template>

<script>
// import MathEquation from '../util/MathEquation.vue'
import Calculation from './Calculation.vue'

export default {
  name: "CalculationProof",
  components: {
//    MathEquation,
    Calculation,
  },

  props: [
    "item",
    "label"
  ]
}

</script>
