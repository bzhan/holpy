<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">integral</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='openFile'>Open</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Calc" left>
          <b-dropdown-item href="#" v-on:click="restart(cur_id)">Restart</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='restore'>Restore</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='save'>Save</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Actions" left>
          <b-dropdown-item href="#" v-on:click='simplify'>Simplify</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='applyLinearity'>Apply linearity</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='applyCommonIntegrals'>Apply common integrals</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='substitution'>Substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='integrateByParts'>Integrate by parts</b-dropdown-item>          
          <b-dropdown-item href="#" v-on:click='polynomialDivision'>Polynomial division</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <div id="content">
      <div v-for="(item, index) in content" :key="index" style="margin:5px 10px">
        <div>{{item.name}}:</div>
        <MathEquation
          v-on:click.native="initialize(index)"
          v-bind:data="'\\(' + item._problem_latex + '\\)'"
          style="cursor:pointer"/>
      </div>
    </div>
    <div id="calc">
      <div v-for="(step, index) in cur_calc" :key="index">
        <span>Step {{index+1}}:</span>
        <MathEquation class="calc-equation" v-bind:data="'\\(' + step.latex + '\\)'"/>
        <MathEquation class="calc-reason" v-if="'_latex_reason' in step" v-bind:data="step._latex_reason"/>
        <span class="calc-reason" v-else>{{step.reason}}</span>
      </div>
    </div>
    <div id="dialog">
      <div v-if="query_mode === 'substitution'">
        <div>
          <label>Substitute</label>
          <input v-model="subst_data.var_name" style="margin:0px 5px;width:25px">
          <label>for</label>
          <input v-model="subst_data.expr" style="margin:0px 5px;width:100px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doSubstitution">OK</button>
        </div>
      </div>
      <div v-if="query_mode === 'byparts'">
        <div>
          <MathEquation data="Choose \(u\) and \(v\) such that \(u\cdot\mathrm{d}v\) is the integrand."/>
        </div>
        <div>
          <MathEquation data="u ="/>
          <input v-model="byparts_data.parts_u" style="margin:0px 5px;width:100px">
          <MathEquation data="v ="/>
          <input v-model="byparts_data.parts_v" style="margin:0px 5px;width:100px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doIntegrateByParts">OK</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import MathEquation from './util/MathEquation'

export default {
  name: 'Integral',
  components: {
    MathEquation,
  },

  props: [
  ],

  data: function () {
    return {
      filename: 'test',    // Currently opened file
      content: [],         // List of problems
      cur_id: undefined,   // ID of the selected item
      cur_calc: [],        // Current calculation
      query_mode: undefined,  // Currently performing which query

      subst_data: {
        var_name: '',  // name of new variable u
        expr: ''       // expression to substitute for u
      },

      byparts_data: {
        parts_u: '',   // value of u
        parts_v: ''    // value of v
      }
    }
  },

  methods: {
    openFile: async function () {
      const data = {
        filename: this.filename
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-open-file", JSON.stringify(data))
      this.content = response.data.content
    },

    initialize: async function (index) {
      this.cur_id = index
      if ('calc' in this.content[index]) {
        this.restore()
      } else {
        this.restart()
      }
    },

    restart: async function () {
        const data = {
          problem: this.content[this.cur_id].problem
        }
        const response = await axios.post("http://127.0.0.1:5000/api/integral-initialize", JSON.stringify(data))
        this.cur_calc = [response.data]
        this.query_mode = undefined
    },

    restore: function () {
      this.cur_calc = Array.from(this.content[this.cur_id].calc)  // create copy
      this.query_mode = undefined
    },

    save: async function () {
      if (this.filename === undefined)
        return;

      if (this.cur_id === undefined)
        return;

      this.content[this.cur_id].calc = this.cur_calc;
      const data = {
        filename: this.filename,
        content: this.content
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-save-file", JSON.stringify(data))

      if (response.data.status === 'success') {
          alert("Saved " + this.content[this.cur_id].name)
      }
    },

    simplify: async function () {
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-simplify", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    applyLinearity: async function () {
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-linearity", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    applyCommonIntegrals: async function () {
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-common-integral", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    substitution: function () {
      if (this.cur_calc.length === 0)
        return;

      this.query_mode = 'substitution'
    },

    doSubstitution: async function () {
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text,
        var_name: this.subst_data.var_name,
        expr: this.subst_data.expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-substitution", JSON.stringify(data))
      this.cur_calc.push(response.data)
      this.query_mode = undefined
      this.subst_data = {var_name: '', expr: ''}
    },

    integrateByParts: function () {
      if (this.cur_calc.length === 0)
        return;

      this.query_mode = 'byparts'
    },

    doIntegrateByParts: async function () {
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text,
        parts_u: this.byparts_data.parts_u,
        parts_v: this.byparts_data.parts_v
      }

      const response = await axios.post("http://127.0.0.1:5000/api/integral-integrate-by-parts", JSON.stringify(data))
      this.cur_calc.push(response.data)
      this.query_mode = undefined
      this.byparts_data = {parts_u: '', parts_v: ''}
    },

    polynomialDivision: async function () {
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-polynomial-division", JSON.stringify(data))
      this.cur_calc.push(response.data)
    }
  },

  created: function () {
    this.openFile()
  }
}
</script>

<style scoped>

.calc-reason {
    margin-left: 50px;
}

.calc-equation {
    margin-left: 20px;
}

#content {
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

#calc {
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

#dialog {
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