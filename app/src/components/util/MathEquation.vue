<template>
  <span ref="mathJaxEl" v-html="data" class="e-mathjax"></span>
</template>

<script type="text/javascript">

export default {
  name: 'MathEquation',
  props: [
    'data'
  ],
  
  watch:{
    'window.MathJax' () {
      this.renderMathJax()
    },
    
    'data' () {
      this.renderMathJax()
    }
  },
  
  updated (){
    this.renderMathJax()
  },
  
  mounted() {
    this.renderMathJax()
  },

  methods:{
    renderMathJax() {
      if (window.MathJax) {
        window.MathJax.Hub.Queue(["Typeset", window.MathJax.Hub,this.$refs.mathJaxEl]);
      }
    }
  }
}
</script>
