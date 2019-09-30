<template>
  <div>
    <span class="keyword">{{item.ty === 'def.ind' ? 'fun' : 'inductive'}}</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
    <span class="keyword">where</span>&nbsp;
    <a href="#" style="font-style:italic;color:brown"
       v-on:click="$emit('edit')">edit</a>
    <span v-for="(v, i) in item.rules" v-bind:key=i>
      <br><span class="item-text indented-text" v-html="Util.highlight_html(v.prop_hl)"></span>
    </span>
  </div>    
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'Inductive',

  props: [
    "item"
  ],

  created() {
    this.Util = Util
  }
}
</script>
