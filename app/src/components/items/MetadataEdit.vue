<template>
  <form>
    <pre class="test-width"/>
    <div>
      <label class="keyword">theory</label>
      <input spellcheck="false" v-model="name" class="form-element"
             min-width="300" ref="name">
    </div>
    <div>
      <label class="keyword">imports</label>
      <textarea spellcheck="false" v-model="imports" class="form-element"
                min-width="300" ref="imports"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">Description:</label><br>
      <textarea spellcheck="false" v-model="description" class="form-element unicode-replace"
                min-width="300" ref="description"/>
    </div>
  </form>
</template>

<script>
import Util from './../../../static/js/util.js'

export default {
  name: 'MetadataEdit',
  props: [
    "theory"
  ],

  data: function () {
    return {
      name: this.theory.name,
      imports: this.theory.imports.join('\n'),
      description: this.theory.description
    }
  },

  mounted() {
    Util.adjust_input_size(this.$refs.name)
    Util.adjust_input_size(this.$refs.imports)
    Util.adjust_input_size(this.$refs.description)
  },

  created() {
    this.Util = Util
  }
}
</script>
