<template>
  <div id="wrap">
    <div id="left-con" class="left-con">
      <div id="pro-ver" class="total left">
        <label for="files" class="choose-file">Please choose a file</label>
        <input type="file" id="files" @change="get_file($event)">
        <div id="program-ver" class="program-ver">
          <div v-for="vcg in file_data" :key="vcg.num" @click="init_program($event)">
            <textarea readonly="readonly" class="code-content con" :name="vcg.num" v-model="vcg.com"></textarea>
          </div>
        </div>
      </div>
      <div id="ver-display" class="right">
        <br><pre class="display-con">{{ program }}</pre>
        <br><pre class="display-res">{{ proof_stat }}</pre>
        <div v-show="proof_process" class="proofArea">
          <proof-area :proof_data="proof"/>
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
      proof_stat: '',         // Statistics for the current program
      proof_process: false,   // Whether conducting a proof
      proof: undefined,       // Data for the current proof
    }
  },
  methods: {
    // Initialize program verification for a program
    init_program: function (e) {
      let num = Number(e.currentTarget.children[0].name)
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/program_verify',
        data: this.file_data[num]
      }).then((res) => {
        this.program = res.data['program']
        this.proof_stat = res.data['proof_stat'][0]
        let failureNum = Number(res.data['proof_stat'][1])
        if (failureNum !== 0) {
          this.proof_process = true
          this.proof = this.file_data[num]
        } else {
          this.proof_process = false
        }
      })
    },

    get_file: function (e) {
      let fileName = e.target.files[0].name
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/get_file',
        data: {'file_name': fileName}
      }).then((res) => {
        this.file_data = res.data['file_data']
      })
    }
  }
}
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
  div#wrap{
    background: #F8F8F8;
    /*overflow: hidden;*/
  }
  div.total{
    margin-left:1%;
  }

  div.program-ver {
    margin-top: 10%;
  }

  div.proofArea {
    width: 80%;
    margin-left: 4%;
    margin-top: 3%;
  }

  .left{
    height: 100vh;
    width: 30%;
    background: none;
    border-right: solid 1px;
    overflow-y: scroll;
    overflow-x: hidden;
  }

  .right{
    width: 70%;
    position: absolute;
    left: 30%;
    right:0;
    top:0;
    background: none;
    height:100vh;
    overflow-y: scroll;
    overflow-x: hidden;
  }

  .display-con{
    margin-left: 5%;
    margin-top: 5%;
    font-size: 20px;
    font-family: Consolas, monospace;
  }

  label.choose-file{
    position: relative;
    top: 4%;
    font-size: 25px;
    background: #F0F0F0;
    color: black;
    border: solid 1px;
    border-radius: 4px;
    width: 8%;
  }

  label.choose-file:hover {
    background-color: white
  }

  #files {
    display: none;
  }

  .display-res {
    margin-left: 5%;
  }

  .con{
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
