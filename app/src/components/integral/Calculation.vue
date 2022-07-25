<template>
  <div>
    <div v-for="(step, index) in steps" :key="index">
      <div v-if="step.type === 'CalculationStep'">
        <CalculationStep v-bind:step="step"/>
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
  ]
}

</script>
