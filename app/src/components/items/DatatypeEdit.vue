<template>
  <form>
    <span>
      <label class="keyword">datatype</label>
      <ExpressionEdit v-model="item.edit_type" min-width="50" single-line/>
      <span class="form-element">=</span>
    </span>
    <div style="margin-top:5px">
      <ExpressionEdit v-model="item.constrs_lines" min-width="200"/>
    </div>
    <pre class="ext-output">{{item.ext}}</pre>
  </form>
</template>

<script>
export default {
  name: 'DatatypeEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          edit_type: "",
          constrs_lines: ""
        },
        JSON.parse(JSON.stringify(this.old_item)))
    }
  }
}
</script>