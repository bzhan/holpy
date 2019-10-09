<template>
  <form>
    <pre class="test-width"/>
    <div>
      <label class="keyword">theory</label>
      <ExpressionEdit v-model="name" single-line/>
    </div>
    <div>
      <label class="keyword">imports</label>
      <ExpressionEdit v-model="imports"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">Description:</label><br>
      <ExpressionEdit v-model="description"/>
    </div>
  </form>
</template>

<script>
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
  }
}
</script>
