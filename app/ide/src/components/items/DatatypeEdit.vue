<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">datatype</label>
      <input spellcheck="false" v-model="item.edit_type" class="form-element"
             min-width="50" ref="edit_type">
      <span class="form-element">=</span>
    </span>
    <div style="margin-top:5px">
      <textarea spellcheck="false" v-model="item.constrs_lines" class="form-element unicode-replace"
                min-width="200" ref="constrs"></textarea>
    </div>
    <div style="margin-top:7px">
        <pre>{{item.ext_output}}</pre>
    </div>
  </form>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'DatatypeEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: $.extend(true, {
        edit_type: "",
        constrs_lines: ""
      }, this.old_item)
    }
  },

  mounted() {
    Util.adjust_input_size(this.$refs.edit_type)
    Util.adjust_input_size(this.$refs.constrs)
  },
  
  created() {
    this.Util = Util
  }
}
</script>