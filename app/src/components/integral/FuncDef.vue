<template>
  <div>
    <span class="keyword">definition</span>&nbsp;
    <span>{{eq}}</span>
    <MathEquation/>
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
    "eq"
  ]
}

</script>
