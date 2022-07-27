<template>
  <div class="indented-label">
    <span class="math-text">{{label}}.</span>&nbsp;
    <div>
      <span class="math-text">Show</span><br/>
      <MathEquation v-bind:data="'\\(' + item.latex_goal + '\\)'" class="indented-text"/>
      <div v-if="'proof' in item">
        <div v-if="item.proof.type === 'CalculationProof'">
          <CalculationProof v-bind:item="item.proof" v-bind:label="label"/>
        </div>
        <div v-if="item.proof.type === 'InductionProof'">
          <InductionProof v-bind:item="item.proof" v-bind:label="label"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'
import InductionProof from './InductionProof.vue'

export default {
  name: "Goal",
  components: {
    MathEquation,
    CalculationProof,
    InductionProof,
  },

  props: [
    "item",
    "label"
  ]
}

</script>
