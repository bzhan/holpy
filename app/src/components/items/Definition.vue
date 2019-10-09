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

export default {
  name: 'Definition',

  props: [
    "item"
  ],
}
</script>
