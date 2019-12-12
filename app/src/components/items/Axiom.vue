<template>
  <div>
    <span class="keyword">axiom</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:&nbsp;
    <a href="#" title="edit" v-on:click="$emit('edit')" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
    <br>
    <span v-if="'prop' in item">
      <span v-for="(line, i) in item.prop" v-bind:key=i>
        <Expression class="indented-text" v-bind:line="line" :editor="editor"/><br>
      </span>
    </span>
  </div>
</template>

<script>

export default {
  name: 'Axiom',

  props: [
    "item",
    "editor",
  ],

}
</script>
