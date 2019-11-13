<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">holpy</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='new_file'>New</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='open_file'>Open</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='load_file'>Refresh</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Items" left>
          <b-dropdown-item href="#" v-on:click='remove_selected'>Remove selected</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='item_move_up'>Move up<span style="float:right;color:dimgrey">Ctrl+↑</span></b-dropdown-item>
          <b-dropdown-item href="#" style="width:170px" v-on:click='item_move_down'>Move down<span style="float:right;color:dimgrey">Ctrl+↓</span></b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Proof" left>
          <b-dropdown-item href="#" v-on:click='undo_move'>Undo move</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='apply_cut'>Insert goal</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='apply_cases'>Apply cases</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='apply_induction'>Apply induction</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='introduction'>Introduction</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='new_var'>New variable</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='apply_backward_step'>Apply backward step</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='apply_forward_step'>Apply forward step</b-dropdown-item>          
          <b-dropdown-item href="#" v-on:click='rewrite_goal'>Rewrite goal</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='rewrite_fact'>Rewrite fact</b-dropdown-item>          
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Setting" left>
          <b-dropdown-item href='#' v-on:click='toggle_profile'>{{profile ? 'Profile on' : 'Profile off'}}</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-form>
          <b-button style="margin-left:10px" variant="primary" v-on:click="add_item">New</b-button>
          <b-form-select style="margin-left:10px" v-model='add_type' :options="add_type_options"/>
          <b-form-select style="margin-left:10px" v-model='add_pos' :options="add_pos_options"/>
        </b-nav-form>
        <span style="margin-left:20px;align-self:center">Opened file: {{ filename }}</span>
        <b-button style="margin-left:10px;align-self:center" variant="primary"
                  v-on:click='load_file'>
          <v-icon name="sync-alt"/>
        </b-button>
      </b-navbar-nav>
    </b-navbar>
    <div id="theory-list" v-show="ref_proof === undefined">
      <Content v-if="filelist !== undefined"
               v-bind:filelist="filelist"
               v-on:select-theory="onSelectTheory"
               ref="content"/>
    </div>
    <div id="proof-context" v-show="ref_proof !== undefined">
      <ProofContext v-bind:ref_proof="ref_proof" ref="context"/>
    </div>
    <div id="theory-content">
      <Theory v-bind:theory="theory"
              v-bind:ref_status="ref_status"
              v-bind:ref_context="ref_context"
              :editor="editor"
              v-on:set-message="onSetMessage"
              v-on:set-proof="handle_set_proof"
              v-on:query="handle_query"
              v-on:goto-link="handleGoToLink"
              ref="theory"/>
    </div>
    <div id="message" v-show="ref_proof === undefined">
      <Message v-bind:message="message" ref="message"/>
    </div>
    <div id="status" v-show="ref_proof !== undefined && query === undefined">
      <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>
    </div>
    <div id="query" v-show="ref_proof !== undefined && query !== undefined">
      <ProofQuery v-bind:query="query"
                  v-on:query-ok="handle_query_ok"
                  v-on:query-cancel="handle_query_cancel"/>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Theory from './Theory'
import Content from './Content'
import Message from './util/Message'
import ProofStatus from './proof/ProofStatus'
import ProofQuery from './proof/ProofQuery'
import ProofContext from './proof/ProofContext'

export default {
  name: 'Editor',
  components: {
    Theory,
    Content,
    Message,
    ProofStatus,
    ProofQuery,
    ProofContext
  },

  props: [
  ],

  data: function () {
    return {
      filelist: [],
      filename: undefined,
      theory: undefined,
      message: undefined,

      // References to the current proof area, proof status, and
      // proof context
      ref_proof: undefined,
      ref_status: undefined,
      ref_context: undefined,

      // Reference to itself
      editor: undefined,

      // Query information
      query: undefined,

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
      ],

      // Settings
      profile: false,
    }
  },

  created: function () {
    this.editor = this
    this.load_filelist()
  },

  methods: {
    handle_set_proof: function (ref_proof) {
      this.ref_proof = ref_proof
    },

    handle_query: function (query) {
      this.query = query
    },

    handle_query_ok: function (vals) {
      this.query.resolve(vals)
      this.query = undefined
    },

    handle_query_cancel: function () {
      this.query.resolve(undefined)
      this.query = undefined
    },

    handleGoToLink: async function (filename, index) {
      if (filename !== this.filename) {
        this.filename = filename
        await this.load_file()
      }
      if (index !== undefined) {
        this.$refs.theory.handle_select(index)
      }
    },

    toggle_profile: function () {
      this.profile = !this.profile
    },

    load_filelist: async function () {
      var response = undefined;
      const data = {
        username: this.$state.user
      }
      try {
        response = await axios.post('http://127.0.0.1:5000/api/find-files', JSON.stringify(data))
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

    new_file: function () {
      const filename = prompt("Name of the theory")
      this.theory = {
        name: filename,
        imports: [],
        description: '',
        content: []
      }
      this.filelist.push(filename)
      this.filelist.sort()
    },

    open_file: function () {
      this.filename = prompt("Open file")
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
      if (this.filename === undefined) {
        return
      }
      const data = JSON.stringify({
        username: this.$state.user,
        filename: this.filename,
        profile: this.profile,
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

    item_move_up: function () {
      this.$refs.theory.item_move_up()
    },

    item_move_down: function () {
      this.$refs.theory.item_move_down()
    },

    add_item: function () {
      this.$refs.theory.add_item(this.add_type, this.add_pos)
    },

    undo_move: function() {
      this.ref_proof.undo_move()
    },

    apply_cut: function () {
      this.ref_proof.apply_method('cut')
    },

    apply_cases: function () {
      this.ref_proof.apply_method('cases')
    },

    apply_induction: function () {
      this.ref_proof.apply_method('induction')
    },

    introduction: function () {
      this.ref_proof.apply_method('introduction')
    },

    new_var: function () {
      this.ref_proof.apply_method('new_var')
    },

    apply_backward_step: function () {
      this.ref_proof.apply_method('apply_backward_step')
    },

    apply_forward_step: function () {
      this.ref_proof.apply_method('apply_forward_step')
    },

    rewrite_goal: function () {
      this.ref_proof.apply_method('rewrite_goal')
    },

    rewrite_fact: function () {
      this.ref_proof.apply_method('rewrite_fact')
    }
  },

  updated() {
    this.ref_status = this.$refs.status
    this.ref_context = this.$refs.context
  }
}
</script>

<style scoped>

#theory-list, #proof-context {
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

#message, #status, #query {
  display: inline-block;
  width: 75%;
  height: 30%;
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
