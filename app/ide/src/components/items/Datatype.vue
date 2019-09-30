<template>
  <div>
    <span class="keyword">datatype</span>&nbsp;
    <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span> =&nbsp;&nbsp;
    <a href="#" style="font-style:italic;color:brown"
       v-on:click="$emit('edit')">edit</a>&nbsp;&nbsp;
    <span v-for="(v, i) in item.constrs_hl" v-bind:key=i>
      <br><span class="item-text indented-text" v-html="Util.highlight_html(v)"></span>
    </span>
  </div>  
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'Datatype',
  
  props: [
    "item"
  ],

  created() {
    this.Util = Util
  }
}
</script>
