<template>
  <form>
    <span>
      <label class="keyword">datatype</label>
      <ExpressionEdit v-model="item.type" min-width="50" single-line/>
      <span class="form-element">=</span>
    </span>
    <div style="margin-top:5px">
      <ExpressionEdit v-model="item.constrs" min-width="200"/>
    </div>
    <pre class="ext-output">{{ext}}</pre>
  </form>
</template>

<script>
export default {
  name: 'DatatypeEdit',
  props: [
    "old_item",
    "ext"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          type: "",
          constrs: ""
        },
        JSON.parse(JSON.stringify(this.old_item)))
    }
  }
}
</script>