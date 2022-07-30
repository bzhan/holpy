<template>
  <div class="indented-label">
    <span class="math-text">{{label}}</span>&nbsp;
    <div>
      <span class="math-text">Show</span>
      <div @click.exact="$emit('select', label)"
           @click.ctrl="$emit('select_fact', label)"
           :class="{selected: selected_item == label,
                    'selected-fact': label in selected_facts}">
        <MathEquation v-bind:data="'\\(' + item.latex_goal + '\\)'" class="indented-text"/>
        <span v-if="'conds' in item && item.conds.length > 0">
          <span class="math-text indented-text">for </span>
          <span v-for="(cond, index) in item.conds" :key="index">
            <span v-if="index > 0">, </span>
            <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
        </span>
      </div>
      <div v-if="'proof' in item">
        <div v-if="item.proof.type === 'CalculationProof'">
          <CalculationProof v-bind:item="item.proof" v-bind:label="label"
                            v-bind:selected_item="selected_item"
                            @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'InductionProof'">
          <InductionProof v-bind:item="item.proof" v-bind:label="label"
                          v-bind:selected_item="selected_item"
                          @select="(lbl) => $emit('select', lbl)"/>
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
    "selected_facts",
  ],

  emits: [
    "select",
    "select_fact"
  ],
}

</script>
