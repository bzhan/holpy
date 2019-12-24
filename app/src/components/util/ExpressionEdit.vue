<template>
  <span>
    <pre class="test-width" ref="test_width"></pre>
    <input v-if="singleLine"
        spellcheck="false" class="form-element"
        v-on:input="handle_input($event)"
        v-on:keydown="replace_unicode($event)"
        v-bind:value="$attrs.value" ref="input"/>
    <textarea v-else
        spellcheck="false" class="form-element"
        v-on:input="handle_input($event)"
        v-on:keydown="replace_unicode($event)"
        v-bind:value="$attrs.value" ref="input"/>
  </span>
</template>

<script>

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

  data: function () {
    return {
      replace_obj: [
        ["\\lambda", "λ"],
        ["%", "λ"],
        ["\\forall", "∀"],
        ["!", "∀"],
        ["\\exists", "∃"],
        ["?", "∃"],
        ["\\and", "∧"],
        ["&", "∧"],
        ["\\or", "∨"],
        ["|", "∨"],
        ["<-->", "⟷"],
        ["-->", "⟶"],
        ["~", "¬"],
        ["\\not", "¬"],
        ["=>", "⇒"],
        ["\\empty", "∅"],
        ["\\Inter", "⋂"],
        ["\\inter", "∩"],
        ["\\Union", "⋃"],
        ["\\union", "∪"],
        ["\\circ", "∘"],
        ["\\in", "∈"],
        ["\\subset", "⊆"],
        ["<=", "≤"],
        [">=", "≥"],
      ]
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
    },

    replace_unicode: function (event) {
      const input = this.$refs.input
      var content = $(input).val().trim();
      var pos = input.selectionStart;
      if (pos !== 0 && event.keyCode === 9) {  // Tab
        var len = '';
        for (let i = 0; i < this.replace_obj.length; i++) {
          var s = this.replace_obj[i][0]
          var repl_s = this.replace_obj[i][1]
          var l = s.length;
          if (content.substring(pos - l, pos) === s) {
            if (event && event.preventDefault) {
              event.preventDefault();
            } else {
              window.event.returnValue = false;
            }
            len = l;
            content = content.slice(0, pos - len) + repl_s + content.slice(pos,);
          }
        }
        if (len) {
          $(input).val(content);
          input.setSelectionRange(pos - len + 1, pos - len + 1);
        }
      }       
    }
  },

  mounted() {
    this.adjust_input_size()
  }
}
</script>

<style scoped>

.test-width {
    display: none;
    padding: 10px;
    font-family: Consolas, monospace;
    font-size: 15px;
}

</style>
