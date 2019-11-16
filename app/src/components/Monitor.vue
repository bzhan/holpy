<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">monitor</b-navbar-brand>
      <span style="margin-left:10px;align-self:center">File </span>
      <b-form-input style="margin-left:10px;display:inline-block;width:200px" v-model="filename" type="text"/>
      <b-button variant="primary" style="margin-left:10px" v-on:click="checkInputTheory">Check</b-button>
      <b-button variant="primary" style="margin-left:10px" v-on:click="checkAllTheory">Check All</b-button>
    </b-navbar>
    <div style="margin:5px 10px">
      Checked {{infos.length}} of {{num_theories}} theories
      <a href="#" v-on:click="unfoldAll">Unfold all </a>
      <a href="#" v-on:click="foldAll">Fold all</a>
    </div>
    <div v-for="(info,index) in infos" v-bind:key="index">
      <div style="margin:5px 10px">
        <span>{{info.filename}}: </span>
        <span>OK {{info.stat.OK}} </span>
        <span>Partial {{info.stat.Partial}} </span>
        <span>Failed {{info.stat.Failed}} </span>
        <span>No steps {{info.stat.NoSteps}} </span>
        <a href="#" v-on:click="info.unfold = !info.unfold">{{info.unfold ? 'fold' : 'unfold'}}</a>
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
      infos: []
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
        filename: filename
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
        this.checkTheory(filelist[i])
      }
    },

    getBackground: function (line) {
      if (line.status === 'OK') {
        return 'lime'
      } else if (line.status === 'NoSteps') {
        return 'aqua'
      } else if (line.status === 'Failed') {
        return 'red'
      } else if (line.status === 'Partial') {
        return 'yellow'
      }
    }
  }
}
</script>