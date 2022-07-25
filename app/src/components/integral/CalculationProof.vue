<template>
  <div>
    <span class="keyword">show</span>&nbsp;
    <span>{{item.goal}}</span>&nbsp;
    <span class="keyword">by calculation</span><br>
    <span class="keyword">LHS</span><br>
    <Calculation v-bind:steps="item.lhs_calc.steps"/>
    <span class="keyword">RHS</span><br>
    <Calculation v-bind:steps="item.rhs_calc.steps"/>
    <MathEquation/>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'
import Calculation from './Calculation.vue'

export default {
  name: "CalculationProof",
  components: {
    MathEquation,
    Calculation,
  },

props: [
    "item"
  ]
}

</script>
