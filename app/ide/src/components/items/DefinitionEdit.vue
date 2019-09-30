<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">
        {{item.ty === 'def' ? 'definition' : (item.ty === 'def.ind' ? 'fun' : 'inductive')}}
      </label>
      <input spellcheck="false" v-model="item.name" class="form-element"
             min-width="50" ref="name">
      <span class="form-element">::</span>
      <input spellcheck="false" v-model="item.type" class="form-element"
             min-width="50" ref="type">
      <label class="keyword">where</label>
    </span>
    <div style="margin-top:3px">
      <textarea spellcheck="false" v-model="item.prop_lines" class="form-element unicode-replace"
                min-width="200" ref="prop"></textarea>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element">
        <input type="checkbox" v-bind:id="'rewrite-check' + id" value="hint_rewrite"
               v-model="item.attributes">
        <label v-bind:for="'rewrite-check' + id">Rewrite</label>
      </span>
    </div>
    <div style="margin-top:7px">
      <pre style="width:100%; background:transparent; text-indent:0">{{item.ext}}</pre>
    </div>
  </form>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'DefinitionEdit',
  props: [
    "old_item"
  ],

  data: function () {
    var res = {
      item: $.extend(true, {}, this.old_item)
    }
    if (!('attributes' in res.item)) {
      res.item.attributes = []
    }
    return res
  },

  computed: {
    id: function () {
      return this.old_item.ty + '.' + this.old_item.name
    }
  },

  mounted() {
    Util.adjust_input_size(this.$refs.name)
    Util.adjust_input_size(this.$refs.type)
    Util.adjust_input_size(this.$refs.prop)
  },

  created() {
    this.Util = Util
  }
}
</script>