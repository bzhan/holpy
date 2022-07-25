<template>
  <div>
    <MathEquation v-bind:data="'\\(=' + step.latex_res + '\\)'"/>&nbsp;&nbsp;&nbsp;
		<span>({{step.rule.str}})</span>
	</div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "CalculationStep",
  components: {
    MathEquation
  },

props: [
		"step",
  ]
}

</script>
