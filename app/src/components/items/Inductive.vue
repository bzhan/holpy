<template>
  <div>
    <span class="keyword">{{item.ty === 'def.ind' ? 'fun' : 'inductive'}}</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <Expression v-bind:line="item.type_hl"/>&nbsp;
    <span class="keyword">where</span>
    <a href="#" v-on:click="$emit('edit')" title="edit" style="margin-left:10px"><v-icon name="edit"/></a>
    <span v-for="(v, i) in item.rules" v-bind:key=i>
      <br><Expression v-bind:line="v.prop_hl" class="indented-text"/>
    </span>
  </div>    
</template>

<script>

export default {
  name: 'Inductive',

  props: [
    "item"
  ],
}
</script>
