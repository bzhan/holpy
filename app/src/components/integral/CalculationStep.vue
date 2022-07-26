<template>
  <div>
    <MathEquation v-bind:data="'\\(=' + step.latex_res + '\\)'" class="indented-text"/>&nbsp;&nbsp;&nbsp;
		<span class="math-text">({{step.rule.str}})</span>
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
