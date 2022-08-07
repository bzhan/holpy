<template>
  <div>
    <div>
      &nbsp;&nbsp;&nbsp;
      <span @click.exact="$emit('select', label)"
            @click.ctrl="$emit('select_fact', label)"
            :class="{selected: selected_item == label,
                     'selected-fact': label in selected_facts}">
        <MathEquation v-bind:data="'\\(' + item.latex_start + '\\)'" class='indented-text'/>
      </span>    
    </div>
    <div v-for="(step, index) in item.steps" :key="index">
      <div v-if="step.type === 'CalculationStep'">
        <CalculationStep v-bind:step="step" v-bind:label="label + (index+1) + '.'"
                         v-bind:selected_item="selected_item"
                         v-bind:selected_facts="selected_facts"
                         @select="(lbl) => $emit('select', lbl)"
                         @select_fact="(lbl) => $emit('select_fact', lbl)"/>
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
    "selected_facts",
  ]
}

</script>
