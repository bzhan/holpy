<template>
  <div>
    <span class="math-text">{{label}}.</span>&nbsp;
    <span class="math-text">Define</span>&nbsp;
    <MathEquation v-bind:data="'\\(' + item.latex_lhs + '\\)'"/>&nbsp;
    <span class="math-text">by</span><br/>
    <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" class="indented-text"/>
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
