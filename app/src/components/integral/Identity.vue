<template>
  <div>
    <span class="keyword">identity</span>&nbsp;
    <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'"/>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "Identity",
  components: {
    MathEquation
  },

props: [
    "item"
  ]
}

</script>
