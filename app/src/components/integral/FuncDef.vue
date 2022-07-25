<template>
  <div>
    <span class="keyword">definition</span>&nbsp;
    <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'"/>
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
    "item"
  ]
}

</script>
