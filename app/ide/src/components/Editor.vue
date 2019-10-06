<template>
  <div>
    <!-- Menu -->
    <b-navbar toggleable="lg" type="light" variant="info">
      <b-navbar-brand href="#">holpy</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file'>Open</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='load_file'>Refresh</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Items" left>
          <b-dropdown-item href="#" v-on:click='remove_selected'>Remove selected</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-form>
          <b-button style="margin-left:10px" variant="primary" v-on:click="add_item">New</b-button>
          <b-form-select style="margin-left:10px" v-model='add_type' :options="add_type_options"/>
          <b-form-select style="margin-left:10px" v-model='add_pos' :options="add_pos_options"/>
        </b-nav-form>
        <span style="margin-left:20px;align-self:center">Opened file: {{ filename }}</span>
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
              v-bind:ref_status="ref_status"
              v-on:set-message="onSetMessage"
              v-on:set-proof="handle_set_proof"
              ref="theory"/>
    </div>
    <div id="message" v-if="ref_proof === undefined">
      <Message v-if="message !== undefined"
               v-bind:message="message"
               ref="message"/>
    </div>
    <div id="status" v-else>
      <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Theory from './Theory'
import Content from './Content'
import Message from './Message'
import ProofStatus from './ProofStatus'
import "./../../static/css/index.css"

export default {
  name: 'Editor',
  components: {
    Theory,
    Content,
    Message,
    ProofStatus,
  },

  props: [
  ],

  data: function () {
    return {
      filelist: [],
      filename: undefined,
      theory: undefined,
      message: undefined,

      // References to the current proof area and proof status
      ref_proof: undefined,
      ref_status: undefined,

      // Type of item to be added
      add_type: 'thm',

      // All possible types
      add_type_options: [
        {value: 'thm', text: "theorem"},
        {value: 'def', text: "definition"},
        {value: 'def.ax', text: "constant"},
        {value: 'def.ind', text: "inductive definition"},
        {value: 'def.pred', text: "inductive predicate"},
        {value: 'thm.ax', text: "axiom"},
        {value: 'type.ind', text: "inductive datatype"}
      ],

      // Location of the new item
      add_pos: 'end',

      // All possible locations
      add_pos_options: [
        {value: 'end', text: "at end"},
        {value: 'before', text: 'before'},
        {value: 'after', text: 'after'}
      ]
    }
  },

  created: function () {
    this.load_filelist()
  },

  methods: {
    handle_set_proof: function (ref_proof) {
      this.ref_proof = ref_proof
    },

    load_filelist: async function () {
      var response = undefined;
      try {
        response = await axios.get('http://127.0.0.1:5000/api/find-files')
      } catch (err) {
        this.message = {
          type: 'error',
          data: 'Server error'
        }
      }
      
      if (response !== undefined) {
        this.filelist = response.data.theories
      }
    },

    open_file: function () {
      this.filename = prompt("Open file")
      this.load_file()
    },

    refresh_file: function () {
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
      this.message = {
        type: 'OK',
        data: 'Loading...'
      }

      var response = undefined;
      try {
        response = await axios.post('http://127.0.0.1:5000/api/load-json-file', data)
      } catch (err) {
        this.message = {
          type: 'error',
          data: 'Server error'
        }
      }

      if (response !== undefined) {
        this.theory = response.data
      }
    },

    remove_selected: function () {
      this.$refs.theory.remove_selected()
    },

    add_item: function () {
      this.$refs.theory.add_item(this.add_type, this.add_pos)
    }
  },

  updated() {
    this.ref_status = this.$refs.status
  }
}
</script>

<style scoped>

#theory-list {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 48px;
  bottom: 0px;
  left: 0px;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 5px;
}

#theory-content {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#message, #status {
  display: inline-block;
  width: 75%;
  height: 25%;
  left: 25%;
  position: fixed;
  top: 70%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

</style>
