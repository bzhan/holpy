<template>
  <form>
    <span>
      <label class="keyword">{{item.ty === 'thm.ax' ? 'axiom' : 'theorem'}}</label>
      <ExpressionEdit v-model="item.name" single-line/>
    </span>
    <div style="margin-top:5px">
      <label class="keyword">fixes</label>
      <ExpressionEdit v-model="item.vars_lines"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">shows</label>
      <ExpressionEdit v-model="item.prop_lines"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'backward-check' + id" value="hint_backward"
               v-model="item.attributes">
        <label v-bind:for="'backward-check' + id">Backward</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'backward1-check' + id" value="hint_backward1"
               v-model="item.attributes">
        <label v-bind:for="'backward1-check' + id">Backward1</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'forward-check' + id" value="hint_forward"
               v-model="item.attributes">
        <label v-bind:for="'forward-check' + id">Forward</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'rewrite-check' + id" value="hint_rewrite"
               v-model="item.attributes">
        <label v-bind:for="'rewrite-check' + id">Rewrite</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'resolve-check' + id" value="hint_resolve"
               v-model="item.attributes">
        <label v-bind:for="'resolve-check' + id">Resolve</label>
      </span>
    </div>
  </form>
</template>

<script>
export default {
  name: 'TheoremEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          attributes: [],
          name: "",
          vars_lines: "",
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
