<template>
  <div style="margin-left:10px;margin-top:10px">
    <span>Variables</span>
    <div style="margin-left:10px" v-for="(T, nm, index) in ctxt" v-bind:key="index">
      <span class="item-text">{{nm}}</span> :: <Expression v-bind:line="T"/>
    </div>
  </div>
</template>

<script>
import Util from './../../static/js/util.js'

export default {
  name: 'ProofContext',

  props: [
  ],

  data: function () {
    return {
      ctxt: undefined
    }
  },

  created() {
    this.Util = Util
  }
}
</script>