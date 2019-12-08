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
          <b-dropdown-item href="#" v-on:click='equationSubst'>Equation Substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='trigtransform'>Trig Substitution</b-dropdown-item>
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
        <MathEquation class="calc-equation"
          v-on:click.native="transfer(step)"
          v-bind:data="'\\(' + step.latex + '\\)'"
          style="cursor:pointer"/>
        <MathEquation class="calc-reason" v-if="'_latex_reason' in step" v-bind:data="step._latex_reason"/>
        <span class="calc-reason" v-else>{{step.reason}}</span>
      </div>
    </div>
    <div id="dialog">
      <div v-if="r_query_mode === 'substitution'">
        <div>
          <label>Substitute</label>
          <input v-model="subst_data.var_name" style="margin:0px 5px;width:100px">
          <label>for</label>
          <input v-model="subst_data.expr" style="margin:0px 5px;width:100px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doSubstitution">OK</button>
        </div>
      </div>
      <div v-if="r_query_mode === 'trig'">
        <label>The initial expression text is {{cur_calc[cur_calc.length-1].text}}.</label>
        <div>
          <label>Write the expression equal to initial ones and make the trig you want to transform surrounded by '$'</label>
          <input v-model="trig_identities_data.old_expr" style="margin:0px 5px;width:200px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doTrigSubstitution">OK</button>
        </div>
      </div>
      <div v-if="r_query_mode === 'display_trig'">
        <div v-for="(step, index) in trig_identities_data.new_expr" :key="index">
          <span>{{index+1}}:</span>
          <MathEquation
            v-on:click.native="transform(step)"
            v-bind:data="'\\(' + step.latex + '\\)'"
            style="cursor:pointer"/>

        </div>
      </div>
      <div v-if="r_query_mode === 'byparts'">
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
      <div v-if="r_query_mode === 'eqsubst'">
        <div>
          <MathEquation v-bind:data="'Write the expression that you think is equal to the \\(' + this.equation_data.old_expr.latex + '\\).'"/>
        </div>
        <div>
          <MathEquation data="new ="/>
          <input v-model="equation_data.new_expr" style="margin:0px 5px;width:100px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doEquationSubst">OK</button>
        </div>
      </div>
    </div>
    <div id="select">
      <div v-if="display_integral === 'separate'">
        <div v-for="(step, index) in sep_int" :key="index">
          <span>{{index+1}}:</span>
          <MathEquation
          v-on:click.native="operate(index)"
          v-bind:data="'\\(' + step.latex + '\\)'"
          style="cursor:pointer"/>
        </div>
        <div style="margin-top:10px">
          <button v-on:click="closeIntegral">Close</button>
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
      r_query_mode: undefined, //record query mode
      display_integral: undefined, //display the separate integral
      sep_int: [], //all separate integrals
      integral_index: undefined, //integral on processing

      allow_click_latex: 0,

      subst_data: {
        var_name: '',  // name of new variable u
        expr: ''       // expression to substitute for u
      },

      byparts_data: {
        parts_u: '',   // value of u
        parts_v: ''    // value of v
      },

      equation_data: {
        old_expr: undefined, //old expression
        new_expr: ''  //new expression
      },
      trig_identities_data: {
        old_expr: undefined, //the equation you need to transform
        new_expr: []
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
        this.clear_separate_integral()
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

    clear_separate_integral: function(){
      this.display_integral = undefined
      this.sep_int = []
      this.integral_index = undefined
      this.r_query_mode = undefined
    },

    simplify: async function () {
      this.clear_separate_integral()
      if (this.cur_calc.length === 0)
        return;
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-simplify", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    applyLinearity: async function () {
      this.clear_separate_integral()
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-linearity", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    applyCommonIntegrals: async function () {
      this.clear_separate_integral()
      if (this.cur_calc.length === 0)
        return;

      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-common-integral", JSON.stringify(data))
      this.cur_calc.push(response.data)
    },

    closeIntegral: async function(){
      //this.clear_separate_integral()
      var integrals = []
      for(var i = 0; i < this.sep_int.length; ++i){
        integrals.push(this.sep_int[i])
      }
      const data = {
        problem: integrals,
        cur_calc: this.cur_calc[this.cur_calc.length - 1].text
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-compose-integral", JSON.stringify(data))
      this.cur_calc.push(response.data)
      this.clear_separate_integral()
    },

    displaySeparateIntegrals: async function(){
      const data = {problem: this.cur_calc[this.cur_calc.length - 1].text}
      const response = await axios.post("http://127.0.0.1:5000/api/integral-separate-integrals", JSON.stringify(data))
      for(var i = 0; i < response.data.length; ++i){
        this.sep_int.push(response.data[i])
      }
      this.display_integral = 'separate'
    },

    operate: function(index){
      this.r_query_mode = this.query_mode
      this.integral_index = index
    },

    transfer: function(step) {
      if (this.allow_click_latex != 0){
        this.equation_data.old_expr = step
      }
    },

    trigtransform: function(){
      if (this.cur_calc.length === 0)
        return;

        this.query_mode = 'trig'
        this.displaySeparateIntegrals()
    },

    doTrigSubstitution: async function(){
      this.trig_identities_data.new_expr = []
      const data = {
        problem: this.sep_int[this.integral_index].text,
        exp: this.trig_identities_data.old_expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-trig-transformation", JSON.stringify(data))
      //this.trig_identities_data.new_expr.push(response.data)
      for(var i=0; i < response.data.length; ++i){
        this.trig_identities_data.new_expr.push(response.data[i])
      }
      this.r_query_mode = 'display_trig'
    },

    transform: function(item){
      //this.cur_calc.push(item)
      this.sep_int[this.integral_index] = item
      this.query_mode = undefined
      this.trig_identities_data.old_expr = ''
      this.trig_identities_data.new_expr = []
    },

    substitution: function () {
      if (this.cur_calc.length === 0)
        return;

      this.query_mode = 'substitution'
      this.displaySeparateIntegrals()
    },

    doSubstitution: async function () {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        var_name: this.subst_data.var_name,
        expr: this.subst_data.expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-substitution", JSON.stringify(data))
      this.sep_int[this.integral_index] = response.data
      this.r_query_mode = undefined
      this.subst_data = {var_name: '', expr: ''}
      this.integral_index = undefined
    },

    integrateByParts: function () {
      if (this.cur_calc.length === 0)
        return;

      this.query_mode = 'byparts'
      this.displaySeparateIntegrals()
    },

    doIntegrateByParts: async function () {
      const data = {
        //problem: this.cur_calc[this.cur_calc.length - 1].text,
        problem: this.sep_int[this.integral_index].text,
        parts_u: this.byparts_data.parts_u,
        parts_v: this.byparts_data.parts_v
      }

      const response = await axios.post("http://127.0.0.1:5000/api/integral-integrate-by-parts", JSON.stringify(data))
      this.sep_int[this.integral_index] = response.data
      this.query_mode = undefined
      this.integral_index = undefined
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
    },

    equationSubst: function() {
      if (this.cur_calc.length === 0)
        return;
      this.allow_click_latex = 1
      this.query_mode = 'eqsubst'
      this.displaySeparateIntegrals()
    },

    doEquationSubst: async function() {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        old_expr: this.equation_data.old_expr.text,
        new_expr: this.equation_data.new_expr
      }

      const response = await axios.post("http://127.0.0.1:5000/api/integral-equation-substitution", JSON.stringify(data))
      this.sep_int[this.integral_index] = response.data
      this.query_mode = undefined
      this.integral_index = undefined
      this.equation_data = {old_expr: undefined, new_expr: ''}
      this.allow_click_latex = 0      
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
  width: 55%;
  height: 30%;
  left: 45%;
  position: fixed;
  top: 70%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

#select {
  display: inline-block;
  width: 20%;
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