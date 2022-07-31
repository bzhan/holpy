<template>
  <div>
    <div v-for="(step, index) in steps" :key="index">
      <div v-if="step.type === 'CalculationStep'">
        <CalculationStep v-bind:step="step" v-bind:label="label + (index+1) + '.'"
                         v-bind:selected_item="selected_item"
                         @select="(lbl) => $emit('select', lbl)"/>
      </div>
    </div>
    <MathEquation/>
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
    "steps",
    "label",
    "selected_item",
  ]
}

</script>
