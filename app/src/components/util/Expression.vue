<template>
  <span class="item-text">
    <ExpressionNode v-for="(node, index) in line" :key="index" :node="node" :editor="editor"/>
  </span>
</template>

<script>
import ExpressionNode from './ExpressionNode'

export default {
  name: 'Expression',
  components: {
    ExpressionNode,
  },

  props: [
    "line",
    "editor"
  ],
}
</script>
