<template>
  <form>
    <span>
      <label class="keyword">
        {{item.ty === 'def.ind' ? 'fun' : 'inductive'}}
      </label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="item.rules"/>
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
          rules: ""
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