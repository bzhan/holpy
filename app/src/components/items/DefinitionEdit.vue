<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">
        {{item.ty === 'def' ? 'definition' : (item.ty === 'def.ind' ? 'fun' : 'inductive')}}
      </label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="item.prop_lines"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'rewrite-check' + id" value="hint_rewrite"
               v-model="item.attributes">
        <label v-bind:for="'rewrite-check' + id">Rewrite</label>
      </span>
    </div>
    <pre class="ext-output">{{item.ext}}</pre>
  </form>
</template>

<script>
export default {
  name: 'DefinitionEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          attributes: [],
          name: "",
          type: "",
          prop_lines: ""
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