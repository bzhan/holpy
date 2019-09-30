<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">constant</label>
      <input spellcheck="false" v-model="item.name" class="form-element"
             min-width="50" ref="name">
      <span class="form-element">::</span>
      <input spellcheck="false" v-model="item.type" class="form-element"
             min-width="100" ref="type">
    </span>
  </form>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'ConstantEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: $.extend(true, {}, this.old_item)
    }
  },

  mounted() {
    Util.adjust_input_size(this.$refs.name)
    Util.adjust_input_size(this.$refs.type)
  },

  created() {
    this.Util = Util
  }
}
</script>
