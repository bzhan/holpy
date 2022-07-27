<template>
  <div class="indented-label">
    <span class="math-text">{{label}}.</span>&nbsp;
    <div>
      <span class="math-text">Show</span>
      <div @click="$emit('select', label)"
           :class="{selected: selected_item == label}">
        <MathEquation v-bind:data="'\\(' + item.latex_goal + '\\)'" class="indented-text"/>
      </div>
      <div v-if="'proof' in item">
        <div v-if="item.proof.type === 'CalculationProof'">
          <CalculationProof v-bind:item="item.proof" v-bind:label="label"
                            v-bind:selected_item="selected_item"
                            @select="(lbl) => $emit('select', lbl)"/>
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
    "label",
    "selected_item",
  ],

  emits: [
    "select"
  ],
}

</script>
