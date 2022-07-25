<template>
  <div>
    <span class="keyword">identity</span>&nbsp;
    <span>{{eq}}</span>
    <MathEquation/>
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
    "eq"
  ]
}

</script>
