<template>
  <div>
    <div>
      &nbsp;&nbsp;&nbsp;
      <MathEquation v-bind:data="'\\(' + item.latex_start + '\\)'" class='indented-text'/>
    </div>
    <div v-for="(step, index) in item.steps" :key="index">
      <div v-if="step.type === 'CalculationStep'">
        <CalculationStep v-bind:step="step" v-bind:label="label + (index+1) + '.'"
                         v-bind:selected_item="selected_item"
                         @select="(lbl) => $emit('select', lbl)"/>
      </div>
    </div>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation'
import CalculationStep from './CalculationStep'

export default {
  name: "Calculation",
  components: {
    MathEquation,
    CalculationStep,
  },

  props: [
    "item",
    "label",
    "selected_item",
  ]
}

</script>
