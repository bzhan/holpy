<template>
  <span>
    <pre class="test-width" ref="test_width"></pre>
    <input v-if="singleLine"
        spellcheck="false" class="form-element unicode-replace"
        v-on:input="handle_input($event)"
        v-bind:value="$attrs.value" ref="input"/>
    <textarea v-else
        spellcheck="false" class="form-element unicode-replace"
        v-on:input="handle_input($event)"
        v-bind:value="$attrs.value" ref="input"/>
  </span>
</template>

<script>
import Util from './../../static/js/util.js'

export default {
  name: 'ExpressionEdit',
  props: {
    minWidth: {
      default: "300",
      type: String
    },

    singleLine: {
      default: false,
      type: Boolean
    }
  },

  methods: {
    adjust_input_size: function () {
      const input = this.$refs.input
      const test_width = this.$refs.test_width
      const text = $(input).val()
      $(test_width).text(text)
      $(input).css('width', $(test_width).css('width'))
      if ($(test_width).width() + 20 < Number(this.minWidth)) {  // +20 to account for padding
        $(input).css('width', this.minWidth + 'px')
      }
      $(input).attr('rows', text.split('\n').length)
    },

    handle_input: function (event) {
      this.$emit('input', event.target.value)
      this.adjust_input_size()
    }
  },

  mounted() {
    this.adjust_input_size()
  }
}
</script>