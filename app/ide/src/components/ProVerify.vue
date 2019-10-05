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
        <Program v-bind:lines="lines" style="margin-top:20px;margin-left:10px" ref="program"/>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import Program from '@/components/Program'

export default {
  name: 'ProVerify',

  components: {
    Program
  },

  data: () => {
    return {
      // Content of the file
      file_data: [],

      // Current program
      lines: '',            
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
      this.$refs.program.undo_move()
    },

    // Initialize program verification for a program
    init_program: async function (num) {
      const data = this.file_data[num]
      let response = await axios.post('http://127.0.0.1:5000/api/program-verify', JSON.stringify(data))
      
      this.lines = response.data.lines
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
