<template>
  <div>
    <!-- Menu -->
    <b-navbar toggleable="lg" type="light" variant="info">
      <b-navbar-brand href="#">verification</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file'>Open file</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Action" left>
          <b-dropdown-item href="#" v-on:click='undo_move'>Undo move</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <div style="margin-top:10px">
      <div class="left">
        <div class="program-ver">
          <div v-for="(vcg,i) in file_data" :key="i" @click="init_program(i)">
            <pre class="code-content content" :name="i">{{vcg.com}}</pre>
          </div>
        </div>
      </div>
      <div class="right">
        <br><pre class="display-con">{{ program }}</pre>
        <br><pre class="display-res">{{ proof_stat }}</pre>
        <div v-show="proof_process" class="proof-area">
          <ProofArea v-bind:vars="vars" v-bind:prop="prop"
                     v-bind:theory_name="'hoare'" v-bind:thm_name="undefined"
                     ref="proof"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import ProofArea from '@/components/ProofArea'

export default {
  name: 'ProVerify',
  components: {
    ProofArea
  },

  data: () => {
    return {
      // Content of the file
      file_data: [],

      // Current program
      program: '',            

      // Number of successful proofs
      proof_success: undefined,
      
      // Number of failed proofs
      proof_failure: undefined,

      // Whether conducting a proof
      proof_process: false,   

      // Data for the current proof
      vars: undefined, prop: undefined
    }
  },

  computed: {
    proof_stat: function () {
      if (this.proof_success !== undefined) {
        return "Proof finished. Success: " + this.proof_success + "  Failure: " + this.proof_failure
      } else {
        return ""
      }
    }
  },

  methods: {
    open_file: async function () {
      var file_name = prompt("Please enter file name", "test")
      const data = {
        file_name: file_name
      }
      var response = await axios.post('http://127.0.0.1:5000/api/get-program-file', JSON.stringify(data))
      this.file_data = response.data.file_data
    },

    undo_move: function() {
      this.$refs.proof.undo_move()
    },

    // Initialize program verification for a program
    init_program: async function (num) {
      const data = this.file_data[num]
      let response = await axios.post('http://127.0.0.1:5000/api/program-verify', JSON.stringify(data))
      
      this.program = response.data.program

      this.proof_success = response.data.proof_success
      this.proof_failure = response.data.proof_failure
      if (this.proof_failure !== 0) {
        this.proof_process = true
        this.vars = response.data.vars
        this.prop = response.data.props[0]
      } else {
        this.proof_process = false
      }
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>

  div.program-ver {
    margin-top: 10%;
  }

  div.proof-area {
    width: 80%;
    margin-left: 4%;
    margin-top: 3%;
  }

  .left {
    display: inline-block;
    width: 30%;
    position: fixed;
    top: 56px;
    bottom: 0%;
    overflow-y: scroll;
    margin-left: 10px;
  }

  .right {
    display: inline-block;
    width: 70%;
    position: fixed;
    top: 56px;
    left: 30%;
    bottom: 0%;
    overflow-y: scroll;
  }

  .display-con {
    margin-left: 5%;
    margin-top: 10px;
    font-size: 20px;
    font-family: Consolas, monospace;
  }

  .display-res {
    margin-left: 5%;
  }

  .content{
    background: #F8F8F8;
    font-size: 20px;
    font-family: Consolas, monospace;
    display: block;
    width: 95%;
    border: 1px solid;
    border-radius: 5px;
    cursor: pointer;
  }

  .code-content{
    margin-top:2%;
    margin-bottom:2%;
    height: auto;
    resize: none;
  }

</style>
