<template>
  <div style="margin-left:10px;margin-top:10px">
    <span>Variables</span>
    <div style="margin-left:10px" v-for="(T, nm, index) in ctxt" v-bind:key="index">
      <span class="item-text">{{nm}}</span> :: <Expression v-bind:line="T"/>
    </div>
  </div>
</template>

<script>

export default {
  name: 'ProofContext',

  props: [
  ],

  data: function () {
    return {
      ctxt: undefined
    }
  },
}
</script>