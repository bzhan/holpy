<template>
  <div>
    <span class="keyword">definition</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <Expression v-if="!('err_type' in item)" v-bind:line="item.type_hl"/>
    <span v-else class="item-text">{{item.type}}</span>
    &nbsp;
    <span class="keyword">where</span>
    <a href="#" title="edit" v-on:click="$emit('edit')" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
    <br>
    <span v-for="(line, i) in item.prop" v-bind:key=i>
      <Expression class="indented-text" v-bind:line="line" :editor="editor"/><br>
    </span>
  </div>
</template>

<script>

export default {
  name: 'Definition',

  props: [
    "item",
    "editor"
  ],
}
</script>
