<template>
  <div>
    <b-navbar toggleable="lg" type="light" variant="info">
      <b-navbar-brand href="#">holpy</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file'>Open</b-dropdown-item>
        </b-nav-item-dropdown>
        <span style="margin-left:10px;align-self:center">Opened file: {{ filename }}</span>
      </b-navbar-nav>
    </b-navbar>
    <div v-if="theory !== undefined" id="theory-content">
      <Theory v-bind:theory="theory"/>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Theory from './Theory.vue'
import "./../../static/css/index.css"

export default {
  name: 'Main',
  components: {
    Theory
  },

  props: [
  ],

  data: function () {
    return {
      filename: 'hoare',
      theory: undefined
    }
  },

  created: function () {
    this.load_file()
  },

  methods: {
    open_file: function () {
      this.filename = prompt("open file")
      this.load_file()
    },

    load_file: async function () {
      const data = JSON.stringify({
        filename: this.filename,
        line_length: 80,
      })
      const response = await axios.post('http://127.0.0.1:5000/api/load-json-file', data)
      this.theory = response.data
    }
  }
}
</script>

<style scoped>

#theory-content {
  margin-top: 10px;
  margin-left: 10px;
}

</style>
