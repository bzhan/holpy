<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">verification</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file_prompt'>Open file</b-dropdown-item>
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
      </b-navbar-nav>
    </b-navbar>
    <div style="margin-top:10px">
      <div id="content" v-show="ref_proof === undefined">
        <div v-for="(item, index) in file_data" :key="index">
          <pre v-if="item.ty === 'vcg'" class="code-content" :name="index"
               @click="init_program(index)" v-html="item.com"/>
        </div>
      </div>
      <div id="proof-context" v-show="ref_proof !== undefined">
        <ProofContext ref="context"/>
      </div>
      <div id="program">
        <Program v-bind:lines="lines" style="margin-top:20px" ref="program"
                 v-bind:ref_status="ref_status" v-bind:ref_context="ref_context"
                 v-on:set-proof="handle_set_proof"
                 v-on:query="handle_query"
                 v-on:save-proof="handle_save_proof"/>
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
  </div>
</template>

<script>
import axios from 'axios'
import Program from './Program'
import ProofStatus from './proof/ProofStatus'
import ProofQuery from './proof/ProofQuery'
import ProofContext from './proof/ProofContext'

export default {
  name: 'ProVerify',

  components: {
    Program,
    ProofStatus,
    ProofQuery,
    ProofContext
  },

  data: function () {
    return {
      // Name of the file
      file_name: '',

      // Content of the file
      file_data: [],

      // Current program
      cur_index: undefined,
      lines: '',

      // References to the current proof area and proof status
      ref_proof: undefined,
      ref_status: undefined,
      ref_context: undefined,

      // Query information
      query: undefined,
    }
  },

  methods: {
    handle_set_proof: function (ref_proof) {
      this.ref_proof = ref_proof
    },

    handle_save_proof: async function (proof) {
      const data = {
        file_name: this.file_name,
        index: this.cur_index,
        proof: proof
      }
      const response = await axios.post('http://127.0.0.1:5000/api/save-program-proof', JSON.stringify(data))
      console.log(response)
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

    open_file_prompt: function () {
      this.open_file(prompt('Please enter file name', 'test'))
    },

    open_file: async function (file_name) {
      this.file_name = file_name
      const data = {
        file_name: file_name
      }
      var response = await axios.post('http://127.0.0.1:5000/api/get-program-file', JSON.stringify(data))
      this.file_data = response.data.file_data
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
    },

    // Initialize program verification for a program
    init_program: async function (index) {
      const data = this.file_data[index]
      let response = await axios.post('http://127.0.0.1:5000/api/program-verify', JSON.stringify(data))
      
      this.cur_index = index
      this.lines = response.data.lines
    }
  },

  mounted() {
    this.open_file('test')
  },

  updated() {
    this.ref_status = this.$refs.status
    this.ref_context = this.$refs.context
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
  #content {
    display: inline-block;
    width: 30%;
    position: fixed;
    top: 48px;
    bottom: 0%;
    overflow-y: scroll;
    padding-top: 20px;
    padding-left: 10px;
  }

  #program {
    display: inline-block;
    width: 70%;
    position: fixed;
    left: 30%;
    top: 48px;
    bottom: 25%;
    overflow-y: scroll;
  }

  #status, #query{
    display: inline-block;
    width: 70%;
    position: fixed;
    left: 30%;
    top: 75%;
    bottom: 0%;
    padding-left: 10px;
    padding-top: 10px;
    overflow-y: scroll;
    border-top-style: solid;
  }

  .code-content {
    background: #F8F8F8;
    font-size: 18px;
    font-family: Consolas, monospace;
    display: block;
    width: 95%;
    border: 1px solid;
    border-radius: 5px;
    cursor: pointer;
  }

</style>
