<template>
  <div>
    <span @click.exact="$emit('select', label)"
          @click.ctrl="$emit('select_fact', label)"
          :class="{selected: selected_item === label,
                   'selected-fact': label in selected_facts}">
      <MathEquation v-bind:data="'\\(=' + step.latex_res + '\\)'" class="indented-text"/>&nbsp;&nbsp;&nbsp;
    </span>
    <span v-if="'latex_str' in step.rule">
      <MathEquation v-bind:data="'(' + step.rule.latex_str + ')'" class="math-text"/>
    </span>
		<span v-else class="math-text">({{step.rule.str}})</span>
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
    "label",
    "selected_item",
    "selected_facts",
  ],
}

</script>
