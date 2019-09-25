<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">theorem</label>
      <input spellcheck="false" v-model="item.name" class="form-element"
             min-width="300" ref="name">
    </span>
    <div style="margin-top:5px">
      <label v-bind:for="'vars' + id" class="keyword">fixes</label>
      <textarea spellcheck="false" v-model="item.vars_lines" class="form-element unicode-replace"
                min-width="300" v-bind:id="'vars' + id" ref="vars"></textarea>
    </div>
    <div style="margin-top:5px">
      <label v-bind:for="'prop' + id" class="keyword">shows</label>
      <textarea spellcheck="false" v-model="item.prop_lines" class="form-element unicode-replace"
                min-width="300" v-bind:id="'prop' + id" ref="prop"></textarea>
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
import Util from './../../../static/js/util.js'

export default {
  name: 'TheoremEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: $.extend(true, {}, this.old_item)
    }
  },

  computed: {
    id: function () {
      return this.old_item.ty + '.' + this.old_item.name
    }
  },

  mounted() {
    Util.adjust_input_size(this.$refs.name)
    Util.adjust_input_size(this.$refs.vars)
    Util.adjust_input_size(this.$refs.prop)
  },

  created() {
    this.Util = Util
  }
}
</script>
