<template>
  <div>
    <span class="keyword">datatype</span>&nbsp;
    <Expression v-bind:line="item.type"/> =
    <a href="#" title="edit" v-on:click="$emit('edit')" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
    <span v-for="(v, i) in item.constrs" v-bind:key=i>
      <br><Expression class="indented-text" v-bind:line="v" :editor="editor"/>
    </span>
  </div>  
</template>

<script>
export default {
  name: 'Datatype',
  
  props: [
    "item",
    "editor"
  ],
}
</script>
