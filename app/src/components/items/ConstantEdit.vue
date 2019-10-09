<template>
  <form>
    <pre class="test-width"></pre>
    <span>
      <label class="keyword">constant</label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="100" single-line/>
    </span>
  </form>
</template>

<script>
export default {
  name: 'ConstantEdit',
  props: [
    "old_item"
  ],

  data: function () {
    return {
      item: Object.assign(
        {
          name: "",
          type: ""
        },
        JSON.parse(JSON.stringify(this.old_item)))
    }
  }
}
</script>
