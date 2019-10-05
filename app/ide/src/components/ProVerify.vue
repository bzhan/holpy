<template>
  <div>
    <!-- Menu -->
    <b-navbar toggleable="lg" type="light" variant="info">
      <b-navbar-brand href="#">verification</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file_prompt'>Open file</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Action" left>
          <b-dropdown-item href="#" v-on:click='undo_move'>Undo move</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <div style="margin-top:10px">
      <div class="left">
        <div v-for="(vcg,i) in file_data" :key="i" @click="init_program(i)">
          <pre class="code-content" :name="i">{{vcg.com}}</pre>
        </div>
      </div>
      <div class="right">
        <Program v-bind:lines="lines" style="margin-top:20px" ref="program"
                 v-bind:ref_status="ref_status" v-on:set-proof="handle_set_proof"/>
      </div>
      <div class="status">
        <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Program from './Program'
import ProofStatus from './ProofStatus'

export default {
  name: 'ProVerify',

  components: {
    Program,
    ProofStatus
  },

  data: () => {
    return {
      // Content of the file
      file_data: [],

      // Current program
      lines: '',

      // References to the current proof area and proof status
      ref_proof: undefined,
      ref_status: undefined
    }
  },

  methods: {
    handle_set_proof: function (ref_proof) {
      this.ref_proof = ref_proof
    },

    open_file_prompt: function () {
      this.open_file(prompt('Please enter file name', 'test'))
    },

    open_file: async function (file_name) {
      const data = {
        file_name: file_name
      }
      var response = await axios.post('http://127.0.0.1:5000/api/get-program-file', JSON.stringify(data))
      this.file_data = response.data.file_data
    },

    undo_move: function() {
      this.ref_proof.undo_move()
    },

    // Initialize program verification for a program
    init_program: async function (num) {
      const data = this.file_data[num]
      let response = await axios.post('http://127.0.0.1:5000/api/program-verify', JSON.stringify(data))
      
      this.lines = response.data.lines
    }
  },

  mounted() {
    this.open_file('test')
  },

  updated() {
    this.ref_status = this.$refs.status
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
  .left {
    display: inline-block;
    width: 30%;
    position: fixed;
    top: 56px;
    bottom: 0%;
    overflow-y: scroll;
    padding-top: 20px;
    padding-left: 10px;
  }

  .right {
    display: inline-block;
    width: 70%;
    position: fixed;
    left: 30%;
    top: 56px;
    bottom: 25%;
    overflow-y: scroll;
  }

  .status {
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
