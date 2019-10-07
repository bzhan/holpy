<template>
  <div align=left>
    <div v-for="name in filelist" v-bind:key=name>
      <a href="#" class="theory-name" v-on:click="$emit('select-theory', name)">{{name}}</a>
    </div>
  </div>
</template>

<script>
export default {
  name: 'Content',
  props: [
    "filelist"
  ]
}
</script>

<style scoped>

.theory-name {
  display: inline-block;
  margin: 5px;
  color: #006000;
}

</style>
