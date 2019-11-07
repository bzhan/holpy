<template>
  <span v-bind:style="{color: get_color(node.color)}"
        v-html="node.text.replace(/ /g, '&nbsp;')"
        v-on:click.ctrl="handleClick($event)"
        @mouseenter.ctrl="handleMouseEnter"
        @mouseleave="handleMouseLeave"
        v-bind:class="{onhover: hover}"/>
</template>

<script>
import axios from 'axios'

export default {
  name: 'ExpressionNode',
  props: [
    "node",
    "editor"
  ],

  data: function () {
    return {
      hover: false
    }
  },

  methods: {
    handleMouseEnter: function () {
      if ('link_ty' in this.node)
        this.hover = true
    },

    handleMouseLeave: function () {
      if ('link_ty' in this.node)
        this.hover = false
    },

    get_color: function (x) {
      if (x === 0) { // normal
        return 'black'
      } else if (x === 1) {  // bound
        return '#006000'
      } else if (x === 2) { // var
        return 'blue'
      } else if (x === 3) { // tvar
        return 'purple'
      } else if (x === 4) {
        return 'silver'
      } else if (x === 5) {
        return 'red'
      } else if (x === 6) {
        return 'green'
      }
    },

    handleClick: async function () {
      if ('link_ty' in this.node) {
        var name = this.node.link_name
        if (name === '') {
          name = this.node.text
        }
        const data = {
          username: this.$state.user,
          filename: this.editor.filename,
          ext_ty: this.node.link_ty,
          name: name
        }
        console.log(data)
        const response = await axios.post('http://127.0.0.1:5000/api/find-link', JSON.stringify(data))
        console.log(response.data)
        if ('filename' in response.data) {
          this.editor.handleGoToLink(response.data.filename, response.data.index)
        }
      }
    }
  }
}
</script>

<style scoped>

.onhover {
  text-decoration: underline;
  cursor: pointer;
}

</style>
