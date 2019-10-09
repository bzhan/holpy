<template>
  <div>
    <span class="keyword">constant</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <Expression v-bind:line="item.type_hl"/>&nbsp;
    <a href="#" title="edit" v-on:click="$emit('edit')" style="margin-left:10px">
      <v-icon name="edit"/>
    </a>
  </div>
</template>

<script>

export default {
  name: 'Constant',

  props: [
    "item"
  ],
}
</script>