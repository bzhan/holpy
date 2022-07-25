<template>
  <div>
		<span>= {{res}} &nbsp;&nbsp;&nbsp;</span>
		<span>({{str}})</span>
		<MathEquation/>
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
    "res",
		"str"
  ]
}

</script>
