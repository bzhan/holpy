<template>
  <div>
    <span class="math-text">by calculation</span><br/>
    <span class="math-text">{{label}}.1.</span>&nbsp;
    <span class="math-text">LHS: </span>
    <span @click="$emit('select', label + '.1')"
          :class="{selected: selected_item == label + '.1'}">
      <MathEquation v-bind:data="'\\(' + item.lhs_calc.latex_start + '\\)'"/>
    </span>
    <Calculation v-bind:steps="item.lhs_calc.steps" v-bind:label="label + '.1'"
                 v-bind:selected_item="selected_item"
                 @select="(lbl) => $emit('select', lbl)"/>
    <span class="math-text">{{label}}.2.</span>&nbsp;
    <span class="math-text">RHS: </span>
    <span @click="$emit('select', label + '.2')"
          :class="{selected: selected_item == label + '.2'}">
      <MathEquation v-bind:data="'\\(' + item.rhs_calc.latex_start + '\\)'"/>
    </span>    
    <Calculation v-bind:steps="item.rhs_calc.steps" v-bind:label="label + '.1'"
                 v-bind:selected_item="selected_item"
                 @select="(lbl) => $emit('select', lbl)"/>
  </div>
</template>

<script>
import Calculation from './Calculation.vue'
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "CalculationProof",
  components: {
    Calculation,
    MathEquation
},

  props: [
    "item",
    "label",
    "selected_item",
  ]
}

</script>
