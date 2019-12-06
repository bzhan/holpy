<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">monitor</b-navbar-brand>
      <span style="margin-left:10px;align-self:center">File </span>
      <b-form-input style="margin-left:10px;display:inline-block;width:200px" v-model="filename" type="text"/>
      <b-button variant="primary" style="margin-left:10px" v-on:click="checkInputTheory">Check</b-button>
      <b-button variant="primary" style="margin-left:10px" v-on:click="checkAllTheory">Check All</b-button>
      <b-form-checkbox label="rewrite-file" style="margin-left:10px" v-model="rewrite_file">Rewrite</b-form-checkbox>
    </b-navbar>
    <div style="margin:5px 10px">
      Checked {{infos.length}} of {{num_theories}} theories
      <a href="#" v-on:click="unfoldAll">Unfold all </a>
      <a href="#" v-on:click="foldAll">Fold all</a>
    </div>
    <div v-for="(info,index) in infos" v-bind:key="index">
      <div v-if="info.stat !== undefined" style="margin:5px 10px">
        <span>{{info.filename}}: </span>
        <span>OK {{info.stat.OK}} </span>
        <span>Partial {{info.stat.Partial}} </span>
        <span v-bind:style="{background:info.stat.Failed > 0 ? 'red' : 'white'}">Failed {{info.stat.Failed}} </span>
        <span>No steps {{info.stat.NoSteps}} </span>
        <span>Proof OK {{info.stat.ProofOK}} </span>
        <span v-bind:style="{background:info.stat.ProofFail > 0 ? 'red' : 'white'}">Proof Fail {{info.stat.ProofFail}} </span>
        <span>Parse OK {{info.stat.ParseOK}} </span>
        <span v-bind:style="{background:info.stat.ParseFail > 0 ? 'red' : 'white'}">Parse Fail {{info.stat.ParseFail}} </span>
        <span v-bind:style="{background:info.stat.EditFail > 0 ? 'red' : 'white'}">Edit Fail {{info.stat.EditFail}} </span>
        <a href="#" v-on:click="info.unfold = !info.unfold">{{info.unfold ? 'Fold' : 'Unfold'}} </a>
        <a href="#" v-on:click="recheckTheory(index)">Recheck</a>
      </div>
      <div v-else style="margin:5px 10px">
        <span>{{info.filename}}: Server error</span>
      </div>
      <table v-if="info.unfold">
        <tr v-for="(line,index) in info.data" v-bind:key="index"
            v-bind:style="{background:getBackground(line)}">
          <td>{{line.name}}</td>
          <td>{{line.status}}</td>
          <td v-if="line.status==='Failed'">{{line.err_type + ' ' + line.err_str}}</td>
          <td v-if="line.status==='OK'">{{line.num_steps + ' steps'}}</td>
          <td v-if="line.status==='Partial'">{{line.num_steps + ' steps'}}</td>
          <td v-if="line.status==='NoSteps'"></td>
          <td v-if="line.status==='ProofOK'"></td>
          <td v-if="line.status==='ProofFail'"></td>
          <td v-if="line.status==='ParseOK'"></td>
          <td v-if="line.status==='ParseFail'"></td>
          <td v-if="line.status==='EditFail'"></td>
        </tr>
      </table>
    </div>
  </div>
</template>

<script>
import axios from 'axios'

export default {
  name: 'Monitor',

  data: function () {
    return {
      filename: '',
      num_theories: 0,
      infos: [],

      rewrite_file: false
    }
  },

  methods: {
    foldAll: function () {
      for (let i = 0; i < this.infos.length; i++) {
        this.infos[i].unfold = false
      }
    },

    unfoldAll: function () {
      for (let i = 0; i < this.infos.length; i++) {
        this.infos[i].unfold = true
      }
    },

    checkInputTheory: function () {
      this.num_theories = 1
      this.infos = []
      this.checkTheory(this.filename)
    },

    checkTheory: async function (filename) {
      const data = {
        username: this.$state.user,
        filename: filename,
        rewrite: this.rewrite_file,
      }
      var response = undefined

      try {
        response = await axios.post('http://127.0.0.1:5000/api/check-theory', JSON.stringify(data))
      } catch (err) {
        this.infos.push({
          filename: filename,
          message: 'Server error'
        })
      }

      if (response !== undefined) {
        this.infos.push({
          filename: filename,
          data: response.data.data,
          stat: response.data.stat,
          unfold: this.num_theories === 1
        })
      }
    },

    recheckTheory: async function (index) {
      const filename = this.infos[index].filename
      const data = {
        username: this.$state.user,
        filename: filename,
        rewrite: this.rewrite_file,
      }
      var response = undefined

      try {
        response = await axios.post('http://127.0.0.1:5000/api/check-theory', JSON.stringify(data))
      } catch (err) {
        this.$set(this.infos, index, {
          filename: filename,
          message: 'Server error'
        })
      }

      if (response !== undefined) {
        this.$set(this.infos, index, {
          filename: filename,
          data: response.data.data,
          stat: response.data.stat,
          unfold: this.infos[index].unfold
        })
      }
    },

    checkAllTheory: async function () {
      var data = {
        username: this.$state.user
      }
      var response = undefined
      response = await axios.post('http://127.0.0.1:5000/api/find-files', JSON.stringify(data))

      const filelist = response.data.theories
      this.num_theories = filelist.length
      this.infos = []
      for (let i = 0; i < filelist.length; i++) {
        await this.checkTheory(filelist[i])
      }
    },

    getBackground: function (line) {
      if (line.status === 'OK' || line.status === 'ProofOK' || line.status === 'ParseOK') {
        return 'lime'
      } else if (line.status === 'NoSteps') {
        return 'aqua'
      } else if (line.status === 'Failed' || line.status === 'ProofFail' ||
                 line.status === 'ParseFail' || line.status === 'EditFail') {
        return 'red'
      } else if (line.status === 'Partial') {
        return 'yellow'
      }
    }
  }
}
</script>