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
    <div id="theory-list">
      <Content v-if="filelist !== undefined"
               v-bind:filelist="filelist"
               v-on:select-theory="onSelectTheory"
               ref="content"/>
    </div>
    <div id="theory-content">
      <Theory v-bind:theory="theory"
              v-on:set-message="onSetMessage"
              ref="theory"/>
    </div>
    <div id="message">
      <Message v-if="message !== undefined"
               v-bind:message="message"
               ref="message"/>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Theory from './Theory.vue'
import Content from './Content.vue'
import Message from './Message.vue'
import "./../../static/css/index.css"

export default {
  name: 'Main',
  components: {
    Theory,
    Content,
    Message
  },

  props: [
  ],

  data: function () {
    return {
      filelist: [],
      filename: undefined,
      theory: undefined,
      message: undefined,
    }
  },

  created: function () {
    this.load_filelist()
  },

  methods: {
    load_filelist: async function () {
      const response = await axios.get('http://127.0.0.1:5000/api/find-files')
      this.filelist = response.data.theories
    },

    open_file: function () {
      this.filename = prompt("open file")
      this.load_file()
    },

    onSelectTheory: function (filename) {
      this.filename = filename
      this.load_file()
    },

    onSetMessage: function (message) {
      this.message = message
    },

    load_file: async function () {
      const data = JSON.stringify({
        filename: this.filename,
        line_length: 80,
      })
      const response = await axios.post('http://127.0.0.1:5000/api/load-json-file', data)
      this.theory = response.data
      this.message = {
        type: 'OK',
        data: 'No errors'
      }
      this.$refs.theory.selected = undefined
    }
  }
}
</script>

<style scoped>

#theory-list {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 56px;
  bottom: 0px;
  left: 0px;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#theory-content {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 56px;
  bottom: 25%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#message {
  display: inline-block;
  width: 75%;
  height: 25%;
  left: 25%;
  position: fixed;
  top: 75%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
}

</style>
