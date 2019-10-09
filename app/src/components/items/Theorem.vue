<template>
  <div>
    <span class="keyword">theorem</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:
    <a href="#" v-on:click="$emit('edit')" title="edit" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
    <a href="#" v-on:click="$emit('proof')" style="margin-left:10px">
      <v-icon v-if="item.proof === undefined" style="color:red" title="no proof" name="times"/>
      <v-icon v-else-if="item.num_gaps > 0" style="color:orange" v-bind:title="item.num_gaps + ' gap(s)'" name="times"/>
      <v-icon v-else name="check" style="color:green" title="qed"/>
    </a>
    <br>
    <span v-if="!('err_type' in item)">
      <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
        <Expression class="indented-text" v-bind:line="line"/><br>
      </span>
    </span>
    <div v-else>
      <div v-if="typeof(item.prop) === 'string'">
        <span class="item-text indented-text">{{item.prop}}</span>
      </div>
      <div v-else>
        <span class="item-text indented-text" v-for="(line, i) in item.prop" v-bind:key=i>
          {{line}}<br>
        </span>
      </div>
    </div>
  </div>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'Theorem',

  props: [
    "item"
  ],

  created() {
    this.Util = Util
  }
}
</script>