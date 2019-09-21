<template>
  <div align=left>
    <pre v-bind:class="{'message-error': message.type === 'error'}">{{message.data}}</pre>
  </div>
</template>

<script>
export default {
  name: 'Message',
  props: [
    "message"
  ]
}
</script>

<style>

.message-error {
  color: red
}

</style>
