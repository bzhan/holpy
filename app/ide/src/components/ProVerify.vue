<template>
  <div>
    <!-- Menu -->
    <b-navbar toggleable="lg" type="light" variant="info">
      <b-navbar-brand href="#">verification</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='open_file'>File</b-dropdown-item>
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
            <textarea readonly="readonly" class="code-content content" :name="i" v-model="vcg.com"></textarea>
          </div>
        </div>
      </div>
      <div class="right">
        <br><pre class="display-con">{{ program }}</pre>
        <br><pre class="display-res">{{ proof_stat }}</pre>
        <div v-if="proof_process" class="proofArea">
          <proof-area :item="proof" ref="proof"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import proofArea from '@/components/ProofArea'

export default {
  name: 'ProVerify',
  components: {
    proofArea
  },

  data: () => {
    return {
      file_data: [],          // Content of the file
      program: '',            // Current program
      proof_success: undefined,  // Number of successful proofs
      proof_failure: undefined,  // Number of failed proofs
      proof_process: false,   // Whether conducting a proof
      proof: undefined,       // Data for the current proof
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
      var res = await axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/get-program-file',
        data: {file_name: file_name}
      })
      this.file_data = res.data.file_data
    },

    undo_move: function() {
      this.$refs.proof.undo_move()
    },

    // Initialize program verification for a program
    init_program: async function (num) {
      let res = await axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/program-verify',
        data: this.file_data[num]
      })
      
      this.program = res.data.program
      this.proof_success = Number(res.data.proof_success)
      this.proof_failure = Number(res.data.proof_failure)
      if (this.proof_failure !== 0) {
        this.proof_process = true
        this.proof = this.file_data[num]
        console.log(this.proof)
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

  div.proofArea {
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
    height:5vh;
    border-radius: 5px;
    cursor: pointer;
  }

  .code-content{
    margin-top:2%;
    margin-bottom:2%;
    height:20vh;
    resize: none;
  }

  .proof_process {
    margin-left: 5%;
    background: none;
    width: 80%;
    height: 350px;
    font-size: 20px;
    font-family: Consolas, monospace;
    outline: none;
    resize: none;
  }

</style>
