<template>
  <div class="indented-label">
    <span class="math-text">{{label}}.</span>&nbsp;
    <div>
      <span class="math-text">Introduce definition</span><br/>
      <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" class="indented-text"/>
    </div>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "FuncDef",
  components: {
    MathEquation
  },

  props: [
    "item",
    "label"
  ]
}

</script>
