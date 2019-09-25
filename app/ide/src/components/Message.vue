<template>
  <div align=left>
    <pre v-bind:class="{'message-error': message.type === 'error'}">{{message.data}}</pre>
    <a href="#" v-if="'trace' in message" v-on:click="show_trace = !show_trace">
      {{show_trace ? 'Hide stack trace' : 'Show stack trace'}}
    </a>
    <pre v-if="show_trace">{{message.trace}}</pre>
  </div>
</template>

<script>
export default {
  name: 'Message',

  props: [
    "message"
  ],

  data: function () {
    return {
      show_trace: false
    }
  }
}
</script>

<style>

.message-error {
  color: red
}

</style>
