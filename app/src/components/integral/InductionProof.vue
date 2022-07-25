<template>
  <div>
    <span class="keyword">show</span>&nbsp;
    <span>{{item.goal}}</span>&nbsp;
    <span class="keyword">by induction on</span>&nbsp;
    <span>{{item.induct_var}}</span><br>
    <span class="keyword">Base case</span><br>
    <CalculationProof v-bind:item="item.base_case"/>
    <span class="keyword">Induction case</span><br>
    <CalculationProof v-bind:item="item.induct_case"/>
    <MathEquation/>
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
    "item"
  ]
}

</script>
