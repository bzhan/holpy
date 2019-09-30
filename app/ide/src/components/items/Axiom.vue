<template>
  <div>
    <span class="keyword">axiom</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:&nbsp;
    <a href="#" style="font-style:italic;color:brown"
       v-on:click="$emit('edit')">edit</a>
    <br>
    <span v-if="'prop_hl' in item">
      <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
        <span class="item-text indented-text" v-html="Util.highlight_html(line)"></span><br>
      </span>
    </span>
  </div>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'Axiom',

  props: [
    "item"
  ],

  created() {
    this.Util = Util
  }
}
</script>
