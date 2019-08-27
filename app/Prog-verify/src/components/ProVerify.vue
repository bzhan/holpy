<template>
  <div id="wrap">
    <div id="left-con" class="left-con">
      <div id="pro-ver" class="total left">
        <label for="files" id="set_file" :style="style_file" @mouseover="button_change" @mouseout="button_change">Please choose a file</label>
        <input type="file" id="files" @change="get_file($event)">
        <div id="program-ver" class="program-ver">
          <div v-for="vcg in file_data" :key="vcg" @click="data_process($event)">
            <textarea readonly="readonly" class="code-content con" :name="vcg.num" v-model="vcg.com"></textarea>
          </div>
        </div>
      </div>
      <div id="ver-display" class="right">
        <br><pre class="display-con">{{ program }}</pre>
        <br><pre class="display-res">{{ proof_stat }}</pre>
        <div v-show="proof_process" class="proofArea">
          {{proof_init_stat}}<br/>
          <proof-area page_num="1" :proof="proof"/>
        </div>
      </div>
    </div>
    <div data-include="display_results"></div>
    <div data-include="edit_area"></div>
    <div data-include="proof_area"></div>
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
      program: '',
      style_file: {background: '#F0F0F0'},
      proof_stat: '',
      file_data: [],
      proof_process: false,
      proof_init_stat: 'ProofArea',
      proof: 'sample proof',
      cl: false
    }
  },
  methods: {
    proof_init: function (dataRelate, that) {
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/init-empty-proof',
        data: {
          'com': dataRelate['com'],
          'pre': dataRelate['pre'],
          'post': dataRelate['post'],
          'vars': dataRelate['vars'],
          'prog_verify': 'true'
        }
      }).then((res) => {
        that.proof = res.data.proof
      })
    },
    data_process: function (e) {
      let num = e.currentTarget.children[0].name
      num = Number(num)
      let dataRelate = this.file_data[num]
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/program_verify',
        data: {
          'com': dataRelate['com'],
          'pre': dataRelate['pre'],
          'post': dataRelate['post'],
          'vars': dataRelate['vars']
        }
      }).then((res) => {
        this.program = res.data['program']
        this.proof_stat = res.data['proof_stat'][0]
        let failureNum = Number(res.data['proof_stat'][1])
        if (failureNum !== 0) {
          let that = this
          this.proof_process = true
          this.proof_init(dataRelate, that)
        } else {
          this.proof_process = false
        }
      })
    },
    button_change: function () {
      this.cl = !this.cl
      this.style_file.background = this.cl ? 'white' : '#F0F0F0'
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

  #set_file{
    position: relative;
    top: 4%;
    font-size: 25px;
    background: #F0F0F0;
    color: black;
    border: solid 1px;
    border-radius: 4px;
    width: 8%;
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
