<template>
  <div v-if="query !== undefined">
    <div>{{query.title}}</div>
    <form>
      <pre class="test-width"></pre>
      <div style="margin-top:5px" v-for="(key, index) in query.fields" v-bind:key=index>
        <label>{{key}}:</label>
        <ExpressionEdit min-width="200" style="margin-left:10px" v-model="vals[key]"/>
      </div>
    </form>
    <button style="margin:5px" v-on:click="handle_ok">OK</button>
    <button style="margin:5px" v-on:click="handle_cancel">Cancel</button>
  </div>
</template>

<script>
export default {
  name: 'ProofQuery',

  props: [
    // Information about the query. This is a dictionary
    // consisting of:
    // title: title of the query
    // fields: information to be entered
    'query',
  ],

  data: function () {
    return {
      vals: {}
    }
  },

  methods: {
    handle_ok: function () {
      this.$emit('query-ok', this.vals)
    },

    handle_cancel: function () {
      this.$emit('query-cancel')
    }
  },

  watch: {
    query: function (new_query) {
      if (new_query === undefined) {
        return
      }

      this.vals = {}
      for (let i = 0; i < new_query.fields.length; i++) {
        this.vals[new_query.fields[i]] = ''
      }
    }
  }
}
</script>
