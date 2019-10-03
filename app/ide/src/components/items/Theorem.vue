<template>
  <div>
    <span class="keyword">theorem</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:&nbsp;&nbsp;
    <a href="#" style="font-style:italic;color:brown"
       v-on:click="$emit('edit')">edit</a>&nbsp;&nbsp;
    <a href="#" v-bind:style="{fontStyle:'italic', color:Util.get_status_color(item)}"
       v-on:click="$emit('proof')">proof</a>
    <br>
    <span v-if="!('err_type' in item)">
      <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
        <span class="item-text indented-text" v-html="Util.highlight_html(line)"></span><br>
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