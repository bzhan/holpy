<template>
  <div>
    <input v-bind:value="value"
           v-on:input="$emit('input', $event.target.value)"
           style="width:500px"/><br/>
    <MathEquation v-bind:data="'\\(' + latex_value + '\\)'"/>
  </div>
</template>

<script>
import axios from 'axios'
import MathEquation from '../util/MathEquation.vue'

export default {
  name: "ExprQuery",
  components: {
    MathEquation
  },

  data: function() {
    return {
      latex_value: undefined
    }
  },

  methods: {
    update_latex_value: async function(val) {
      if (val == '') {
        this.latex_value = undefined
        return
      }
      const data = {
        expr: val
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-expr", JSON.stringify(data))
      if (response.data.status === 'ok') {
        this.latex_value = response.data.latex_expr
      } else {
        this.latex_value = undefined
      }
    }
  },

  watch: {
    value: async function(val) {
      this.update_latex_value(val)
    }
  },

  props: [
    "value",
  ],

  created: function () {
    this.update_latex_value(this.value)
  }
}

</script>
