<template>
  <div>
    <span class="keyword">theorem</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:
    <a href="#" v-on:click="$emit('edit')" title="edit" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
    <a href="#" v-on:click="$emit('proof')" style="margin-left:10px">
      <v-icon v-if="proof === undefined" style="color:red" title="no proof" name="times"/>
      <v-icon v-else-if="num_gaps > 0" style="color:orange" v-bind:title="num_gaps + ' gap(s)'" name="times"/>
      <v-icon v-else name="check" style="color:green" title="qed"/>
    </a>
    <br>
    <span v-for="(line, i) in item.prop" v-bind:key=i>
      <Expression class="indented-text" v-bind:line="line" v-on:goto-item="goto-item"
                  :editor="editor"/><br>
    </span>
  </div>
</template>

<script>

export default {
  name: 'Theorem',

  props: [
    "item",
    "proof",
    "num_gaps",
    "editor",
  ],
}
</script>