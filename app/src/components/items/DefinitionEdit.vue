<template>
  <form>
    <span>
      <label class="keyword">definition</label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="item.prop"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'rewrite-check' + id" value="hint_rewrite"
               v-model="item.attributes">
        <label v-bind:for="'rewrite-check' + id">Rewrite</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'rewrite-sym-check' + id" value="hint_rewrite_sym"
               v-model="item.attributes">
        <label v-bind:for="'rewrite-sym-check' + id">Rewrite (sym)</label>
      </span>
    </div>
    <pre class="ext-output">{{ext}}</pre>
  </form>
</template>

<script>
export default {
  name: 'DefinitionEdit',
  props: [
    "old_item",
    "ext"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          attributes: [],
          name: "",
          type: "",
          prop: ""
        },
        JSON.parse(JSON.stringify(this.old_item)))
    }
  },

  computed: {
    id: function () {
      return this.old_item.ty + '.' + this.old_item.name
    }
  }
}
</script>