<template>
  <div>
    <span class="keyword">constant</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
    <a href="#" title="edit" v-on:click="$emit('edit')" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
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