<template>
  <div>
    <span class="keyword">constant</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
    <a href="#" style="font-style:italic;color:brown"
       v-on:click="$emit('edit')">edit</a>
  </div>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'Constant',

  props: [
    "item"
  ],

  created() {
    this.Util = Util
  }
}
</script>