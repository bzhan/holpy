<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">Integral</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='load_file_list'>Open file</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='insert_integral'>New integral</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Calc" left>
          <b-dropdown-item href="#" v-on:click="back">Back</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="restart(cur_id)">Restart</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='restore'>Restore</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='save'>Save</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Actions" left>
          <b-dropdown-item href="#" v-on:click='slagle'>Slagle</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='superSimplify'>Simplify</b-dropdown-item>          
          <b-dropdown-item href="#" v-on:click='substitution'>Substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='substitution1'>Substitution inverse</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='integrateByParts'>Integrate by parts</b-dropdown-item>          
          <b-dropdown-item href="#" v-on:click='polynomialDivision'>Rewrite fraction</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='equationSubst'>Equation Substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='trigtransform'>Trig Identity</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='unfoldPower'>Unfold power</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='split'>Split Integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='integrateByEquation'>Integrate by equation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='elimAbs'>Eliminate Abs</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <div id="content">
      <div v-if="content_state === false" align=left>
        <div v-for="name in file_list" v-bind:key=name style="margin:5px 10px">
          <a href="#" v-on:click="openFile(name)">{{name}}</a>
        </div>
      </div>
      <div v-if="content_state === true">
        <div v-for="(item, index) in content" :key="index" style="margin:5px 10px">
          <div>{{item.name}}:</div>
          <MathEquation
            v-on:click.native="initialize(index)"
            v-bind:data="'\\(' + item._problem_latex + '\\)'"
            style="cursor:pointer"/>
        </div>
      </div>
    </div>
    <div id="calc">
      <div v-for="(step, index) in cur_calc" :key="index">
        <span>Step {{index+1}}:&nbsp;&nbsp;</span>
        <MathEquation v-bind:data="'\\(' + step.latex + '\\)'"/>
        <MathEquation class="calc-reason" v-if="'_latex_reason' in step && step._latex_reason !== ''" v-bind:data="step._latex_reason"/>
        <span class="calc-reason" v-else>{{step.reason}}</span>
      </div>
    </div>
    <div id="dialog">
      <div v-if="r_query_mode === 'substitution'">
        <div>
          <span>The initial text is {{sep_int[integral_index].text}}</span>
        </div>
        <div>
          <label>Substitute</label>
          <input v-model="subst_data.var_name" style="margin:0px 5px;width:50px">
          <label>for</label>
          <input v-model="subst_data.expr" style="margin:0px 5px;width:200px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doSubstitution">OK</button>
        </div>
        <div>
          <p v-if="seen === true" style="color:red">{{this.error_message}}</p>
        </div>
      </div>
      <div v-if="r_query_mode === 'substitution1'">
        <div>
          <span>The initial text is {{sep_int[integral_index].text}}</span>
        </div>
        <div>
          <label>The variable name: </label>
          <input v-model="subst_data.var_name" style="margin:0px 5px;width:200px">
          <label>The expression: </label>
          <input v-model="subst_data.expr" style="margin:0px 5px;width:200px">
        </div>
        <div>
          <p v-if="seen === true" style="color:red">{{this.error_message}}</p>
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doSubstitution1">OK</button>
        </div>
        <div>
          <p v-if="seen === true" style="color:red">{{this.error_message}}</p>
        </div>
      </div>
      <div v-if="r_query_mode === 'unfoldpower'">
        <lable>Select the power expression you want to unfold.</lable>
        <br>
        <input ref="power" style="width:400px" disabled="disabled" v-model="this.sep_int[integral_index].body">
        <button v-on:click="validation_power">OK</button>  
      </div>
      <div v-if="r_query_mode === 'trig'">
        <label>Select the part you wish to transform to other trignometric functions.</label>
        <br>
        <input id="cloned" ref="mycloned" style="width:500px" disabled="disabled" v-model="this.sep_int[integral_index].body">
        <button v-on:click="validation">OK</button>
        <br>
        <p v-if="seen === true" style="color:red">Illegal selection: "{{this.selected}}" is not a valid expression.</p>
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
          <br/>
          <span>{{sep_int[integral_index].text}}</span>
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
        <div>
          <p v-if="seen === true" style="color:red">{{this.error_message}}</p>
        </div>
      </div>
      <div v-if="r_query_mode === 'eqsubst'">
        <div>Select the part you want to transform to new expression.</div>
        <input ref="rewriten" style="width: 200px" disabled="disabled" v-model="this.sep_int[integral_index].body">
        <button v-on:click="validation1">Validate</button>
        <p v-if="seen === true">Illegal</p>
        <br/>
        <span v-if="seen === false">{{equation_data.rewrite_part}}=</span>
        <input v-if="seen === false" v-model="equation_data.new_expr" style="width: 400px">
        <button v-on:click="rewrite" style="color:red">Rewrite</button>
        <p v-if="rewrite_error_flag === true" style="color:red">The rewrite is invalid.</p>
      </div>
      <div v-if="r_query_mode === 'byequation'">
        <div>
        <MathEquation data="Input the step index you want to put on the eqution' left side."/>
        </div>
        <div>
          <input v-model.number="lhs" type="number" style="margin:0px 5px;width:50px">
        </div>
        <div style="margin-top:10px">
          <button v-on:click="doIntegrateByEquation">OK</button>
        </div>
      </div>
      <div v-if="r_query_mode === 'split'">
        <div>
          <MathEquation v-bind:data="'\\(Write\\ the\\ point\\ you\\ want\\ to\\ split\\ in\\ ' + sep_int[integral_index].latex + '\\)'" />
        </div>
        <div>   
            <input v-model="split_point" style="margin:0px 5px;width:100px">
            <button v-on:click="doSplitIntegral">OK</button>
            <label v-if="split_success === false" style="color:red">Invalid split.</label>
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
      <div v-if="display_integral === 'division'">
        <div v-for="(step, index) in sep_int" :key="index">
          <span>{{index+1}}:</span>
          <MathEquation
          v-on:click.native="doPolynomialDivision(index)"
          v-bind:data="'\\(' + step.latex + '\\)'"
          style="cursor:pointer"/>
        </div>
        <div>
          <p v-if="seen === true" style="color:red">{{this.error_message}}</p>
        </div>
        <div style="margin-top:10px">
          <button v-on:click="closeIntegral">Close</button>
        </div>  
      </div>
      <div v-if="display_integral === 'abs'">
        <div v-for="(step, index) in sep_int" :key="index">
          <span>{{index+1}}:</span>
          <MathEquation
          v-on:click.native="doElimAbs(index)"
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
      filename: 'tongji7',    // Currently opened file
      content: [],         // List of problems
      file_list: [],      //List of integral list
      content_state: undefined, // state of the content panel, if it is true, display the integrals in content,
                                // or else display the json files in file list
      cur_id: undefined,   // ID of the selected item
      cur_calc: [],        // Current calculation
      query_mode: undefined,  // Currently performing which query
      r_query_mode: undefined, //record query mode
      display_integral: undefined, //display the separate integral
      sep_int: [], //all separate integrals
      process_index: undefined,
      integral_index: undefined, //integral on processing
      take_effect: 0,     //Flag for whether a rule takes effect or close on halfway.

      seen: false, //When an error occurs, make the error message can be seen.
      rewrite_error_flag: false, //When the rewrite is invalid, display error warning.

      selected: undefined,
      error_message: undefined,

      subst_data: {
        var_name: '',  // name of new variable u
        expr: ''       // expression to substitute for u
      },

      byparts_data: {
        parts_u: '',   // value of u
        parts_v: ''    // value of v
      },

      equation_data: {
        rewrite_part: undefined, //the expr want to rewrite
        relative_location: undefined,
        absolute_location: undefined,
        new_expr: '',  //new expression
        fail_reason: undefined
      },

      trig_identities_data: {
        old_expr: undefined, //the equation you need to transform
        new_expr: []
      },

      lhs: undefined, //equation left hand side
      split_point: undefined,
      split_success: undefined,
      integral_str: '', // record the input string of new integral
    }
  },

  methods: {

    load_file_list: async function (){
      const response = await axios.post('http://127.0.0.1:5000/api/integral-load-file-list')
      this.file_list = response.data.file_list
      this.content_state = false
    },

    openFile: async function (file_name) {
      const data = {
        filename: file_name
      };
      this.filename = file_name
      const response = await axios.post("http://127.0.0.1:5000/api/integral-open-file", JSON.stringify(data))
      this.content = response.data.content
      this.cur_calc = undefined
      this.content_state = true
    },

    insert_integral: async function (){
      var integration = prompt('Please write the integral', '');
      const data = {
        expr: integration,
        index: this.content.length + 1
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-validate-integral", JSON.stringify(data))
      if(response.data.flag){
        this.content.push(response.data.content)
      }else{
        prompt('Bad input!')
      }
    },

    initialize: async function (index) {
      this.query_mode = undefined
      this.r_query_mode = undefined
      this.display_integral = undefined
      this.cur_id = index
      this.take_effect = 0
      if ('calc' in this.content[index]) {
        this.restore()
      } else {
        this.restart()
      }
    },

    back: function(){
      this.cur_calc.pop()
      this.clear_separate_integral()
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

    validation: async function() {
      let selected = this.sep_int[this.integral_index].body.slice(this.$refs.mycloned.selectionStart, this.$refs.mycloned.selectionEnd);
      let expr_with_dollar = this.sep_int[this.integral_index].body.slice(0, this.$refs.mycloned.selectionStart) + '$' + selected + '$' + this.sep_int[this.integral_index].body.slice(this.$refs.mycloned.selectionEnd);
      this.selected = selected
      const data = {
        integral_location: this.sep_int[this.integral_index].location,
        problem: this.sep_int[this.integral_index].text,
        dollar: expr_with_dollar,
        select: this.selected
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-validate-expr", JSON.stringify(data))
      if(response.data.flag === true){
        for(var i=0; i < response.data["content"].length; ++i){
          this.trig_identities_data.new_expr.push(response.data["content"][i]);
        }
        this.r_query_mode = 'display_trig';
      }else{
        this.seen = true;
      }
    },

    validation_power: async function() {
      let selected = this.sep_int[this.integral_index].body.slice(this.$refs.power.selectionStart, this.$refs.power.selectionEnd);
      let expr_with_dollar = this.sep_int[this.integral_index].body.slice(0, this.$refs.power.selectionStart) + '$' + selected + '$' + this.sep_int[this.integral_index].body.slice(this.$refs.power.selectionEnd);
      const data = {
        integral_location: this.sep_int[this.integral_index].location,
        problem: this.sep_int[this.integral_index].text,
        dollar: expr_with_dollar,
        select: selected
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-validate-power-expr", JSON.stringify(data))
      if(response.data.flag === true){
        this.sep_int[this.integral_index] = response.data;
        this.take_effect = 1;
        this.r_query_mode = undefined;
        this.process_index = this.integral_index;
        this.closeIntegral();
      }else{
        this.seen = true;
      }
    },    

    validation1: async function() {
      //Check if the selected rewrite part is a valid expression, and find the location
      let selected = this.sep_int[this.integral_index].body.slice(this.$refs.rewriten.selectionStart, this.$refs.rewriten.selectionEnd);
      let expr_with_dollar = this.sep_int[this.integral_index].body.slice(0, this.$refs.rewriten.selectionStart) + '$' + selected + '$' + this.sep_int[this.integral_index].body.slice(this.$refs.rewriten.selectionEnd);
      const data = {
        //The first two items can be one thing.
        integral_location: this.sep_int[this.integral_index].location,
        problem: this.sep_int[this.integral_index].text,
        dollar: expr_with_dollar,
        select: selected
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-validate-rewrite", JSON.stringify(data))
      if(response.data.flag === true){
        this.seen = false;
        this.equation_data.rewrite_part = response.data["rewrite"];
        this.equation_data.relative_location = response.data["relative_location"];
        this.equation_data.absolute_location = response.data["absolute_location"];
      }else{
        this.seen = true;
      }
    },

    rewrite: async function() {
      const data = {
        old_expr: this.equation_data.rewrite_part,
        new_expr: this.equation_data.new_expr,
        relative_location: this.equation_data.relative_location,
        absolute_location: this.equation_data.absolute_location,
        problem: this.sep_int[this.integral_index].text
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-rewrite-expr", JSON.stringify(data));
      if(response.data.flag === true){
        this.sep_int[this.integral_index] = response.data;
        this.r_query_mode = undefined;
        this.take_effect = 1;
        this.process_index = this.integral_index;
        this.closeIntegral();
      }else{
        this.rewrite_error_flag = true;
      }
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
      this.display_integral = undefined;
      this.sep_int = [];
      this.integral_index = undefined;
      this.r_query_mode = undefined;
      this.process_index = undefined;
      this.take_effect = 0;
      this.rewrite_error_flag = undefined;
      this.split_success = undefined;
      this.selected = undefined;
      this.error_message = undefined;
      this.seen = undefined;
    },

    clear_input_info: function() {      
      this.byparts_data =  {parts_u: '', parts_v: ''};
      this.equation_data = {new_expr: '', fail_reason: undefined};
      this.trig_identities_data = {old_expr: undefined, new_expr: []};
    },

    simplify: async function () {
      this.clear_separate_integral();
      if (this.cur_calc.length === 0)
        return;
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-simplify", JSON.stringify(data));
      this.cur_calc.push(response.data);
    },

    superSimplify: async function (){
      this.clear_separate_integral();
      if (this.cur_calc.length === 0){
        return;
      }
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-super-simplify", JSON.stringify(data));
      //this.cur_calc.push(response.data);

      this.cur_calc.push(response.data)
    },

    slagle: async function(){
      this.clear_separate_integral();
      if (this.cur_calc.length === 0){
        return;
      }
      const data = {
        problem: this.cur_calc[this.cur_calc.length - 1].text
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-slagle", JSON.stringify(data));
      for(var i = 0; i < response.data.length; ++i){
        this.cur_calc.push(response.data[i])
      }
    },

    elimAbs: function() {
      if(this.cur_calc.length == 0){
        return;
      }
      this.query_mode = 'abs';
      this.displaySeparateIntegrals_abs();
    },

    doElimAbs: async function (index) {
      this.integral_index = index;
      const data = {
        problem: this.sep_int[this.integral_index].text,
        location: this.sep_int[this.integral_index].location
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-elim-abs", JSON.stringify(data))
      this.sep_int[this.integral_index] = response.data;
      this.process_index = this.integral_index;
      this.take_effect = 1;
      this.closeIntegral();
      this.query_mode = undefined;
      this.superSimplify();
    },

    closeIntegral: async function(){
      //this.clear_separate_integral()
      var integrals = []
      for(var i = 0; i < this.sep_int.length; ++i){
        integrals.push(this.sep_int[i])
      }
      if (this.take_effect == 1){
        const data = {
          problem: integrals,
          cur_calc: this.cur_calc[this.cur_calc.length - 1].text,
          index:  this.process_index
        }
        const response = await axios.post("http://127.0.0.1:5000/api/integral-compose-integral", JSON.stringify(data))
        this.cur_calc.push(response.data)        
      }this.clear_separate_integral();
      this.clear_input_info()
    },

    displaySeparateIntegrals: async function(){
      const data = {problem: this.cur_calc[this.cur_calc.length - 1].text}
      const response = await axios.post("http://127.0.0.1:5000/api/integral-separate-integrals", JSON.stringify(data))
      for(var i = 0; i < response.data.length; ++i){
        this.sep_int.push(response.data[i])
      }
      this.display_integral = 'separate'
    },

    displaySeparateIntegrals_division: async function(){
      const data = {problem: this.cur_calc[this.cur_calc.length - 1].text}
      const response = await axios.post("http://127.0.0.1:5000/api/integral-separate-integrals", JSON.stringify(data))
      for(var i = 0; i < response.data.length; ++i){
        this.sep_int.push(response.data[i])
      }
      this.display_integral = 'division'
    },


  displaySeparateIntegrals_abs: async function(){
      const data = {problem: this.cur_calc[this.cur_calc.length - 1].text}
      const response = await axios.post("http://127.0.0.1:5000/api/integral-separate-integrals", JSON.stringify(data))
      for(var i = 0; i < response.data.length; ++i){
        this.sep_int.push(response.data[i])
      }
      this.display_integral = 'abs'
    },

    operate: function(index){
      this.clear_input_info()
      this.r_query_mode = this.query_mode
      // if user want to do substitution,
      // recommend a subst variable.
      if(this.r_query_mode === 'substitution'){
        let current_var = this.sep_int[index]["var_name"];
        if(current_var === "u"){
          this.subst_data.var_name = "v";
        }
        else{
          this.subst_data.var_name = "u";
        }
      }

      this.integral_index = index
    },

    trigtransform: function(){
      if (this.cur_calc.length === 0)
        return;

        this.query_mode = 'trig'
        this.displaySeparateIntegrals()
        this.sep_int = []
    },

    transform: function(item){
      //this.cur_calc.push(item)
      this.sep_int[this.integral_index] = item;
      this.process_index = this.integral_index;
      this.take_effect = 1;
      this.closeIntegral();
      this.query_mode = undefined
      this.trig_identities_data.old_expr = ''
      this.trig_identities_data.new_expr = []
    },

    substitution: function () {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = []
      this.query_mode = 'substitution'
      this.displaySeparateIntegrals()
    },

    doSubstitution: async function () {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        location: this.sep_int[this.integral_index].location,
        var_name: this.subst_data.var_name,
        expr: this.subst_data.expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-substitution", JSON.stringify(data))
      if (response.data.flag === true){
        this.sep_int[this.integral_index] = response.data.log;
        this.r_query_mode = undefined;
        this.subst_data = {var_name: '', expr: ''};
        this.take_effect = 1;
        this.process_index = this.integral_index;
        this.closeIntegral();
        this.integral_index = undefined;
      }
      else{
        this.seen = true;
        this.error_message = response.data.reason;
      }
      
    },

    substitution1: function () {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = [];
      this.query_mode = 'substitution1';
      this.subst_data = {var_name: '', expr: ''};
      this.displaySeparateIntegrals()
    },

    doSubstitution1: async function () {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        location: this.sep_int[this.integral_index].location,
        var_name: this.subst_data.var_name,
        expr: this.subst_data.expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-substitution2", JSON.stringify(data))
      if(response.data.flag === true){
        this.sep_int[this.integral_index] = response.data.log;
        this.r_query_mode = undefined;
        this.subst_data = {var_name: '', expr: ''};
        this.take_effect = 1;
        this.process_index = this.integral_index;
        this.closeIntegral();
        this.integral_index = undefined;
      }
      else{
        this.seen = true;
        this.error_message = response.data.reason;
      }
    },
    
    split: function(){
      if(this.cur_calc.length == 0)
        return;
      this.sep_int = []
      this.query_mode = 'split';
      this.displaySeparateIntegrals();
    },

    doSplitIntegral: async function() {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        point: this.split_point,
        location: this.sep_int[this.integral_index].location
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-split", JSON.stringify(data));
      if(response.data.flag == "success"){
        this.sep_int[this.integral_index] = response.data;
        this.split_success = true;
        this.take_effect = 1;
        this.process_index = this.integral_index;
        this.closeIntegral();
      }else{
        this.split_success = false;
      }
    },
    

    unfoldPower: function () {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = []
      this.query_mode = 'unfoldpower'
      this.displaySeparateIntegrals()
    },

    integrateByParts: function () {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = []
      this.query_mode = 'byparts'
      this.displaySeparateIntegrals()
    },

    doIntegrateByParts: async function () {
      const data = {
        //problem: this.cur_calc[this.cur_calc.length - 1].text,
        problem: this.sep_int[this.integral_index].text,
        parts_u: this.byparts_data.parts_u,
        parts_v: this.byparts_data.parts_v,
        location: this.sep_int[this.integral_index].location
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-integrate-by-parts", JSON.stringify(data))
      if(response.data.flag === true){
        this.sep_int[this.integral_index] = response.data.log;
        this.r_query_mode = undefined;
        this.byparts_data = {parts_u: '', parts_v: ''};
        this.take_effect = 1;
        this.process_index = this.integral_index;
        this.integral_index = undefined;
        this.closeIntegral();
      }
      else{
        this.seen = true;
        this.error_message = response.data.reason;
      }
    },

    integrateByEquation: function(){
      if (this.cur_calc.length === 0)
        return;
      this.r_query_mode = "byequation"
    },

    doIntegrateByEquation: async function(){
      const data = {
        lhs: this.cur_calc[this.lhs - 1].text,
        rhs: this.cur_calc[this.cur_calc.length - 1].text,
        prev_id: this.lhs
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-integrate-by-equation", JSON.stringify(data))
      this.cur_calc.push(response.data);
      this.lhs = undefined;
      this.r_query_mode = undefined;
    }, 

    polynomialDivision: async function() {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = [];
      this.displaySeparateIntegrals_division();
      this.display_integral = "division";
    },

    doPolynomialDivision: async function (index) {
      this.integral_index = index;
      const data = {
        problem: this.sep_int[index].text,
        location: this.sep_int[index].location
      };
      const response = await axios.post("http://127.0.0.1:5000/api/integral-polynomial-division", JSON.stringify(data));
      if(response.data.flag === true){
        this.sep_int[index] = response.data;
        this.take_effect = 1;
        this.process_index = index;
        this.closeIntegral();
      }else{
        this.seen = true;
        this.error_message = response.data.reason;
      }
    },

    equationSubst: function() {
      if (this.cur_calc.length === 0)
        return;
      this.sep_int = []
      this.query_mode = 'eqsubst'
      this.displaySeparateIntegrals()
      this.equation_data.fail_reason = undefined
    },

    doEquationSubst: async function() {
      const data = {
        problem: this.sep_int[this.integral_index].text,
        new_expr: this.equation_data.new_expr
      }

      const response = await axios.post("http://127.0.0.1:5000/api/integral-equation-substitution", JSON.stringify(data))
      if (response.data.flag == 'success'){
        this.sep_int[this.integral_index] = response.data
        this.r_query_mode = undefined
        this.integral_index = undefined
        this.equation_data = {new_expr: '', fail_reason: undefined}
        this.take_effect = 1      
      }else{
        this.equation_data.fail_reason = response.data._latex_reason
      }
    }


  },

  created: function () {
    this.load_file_list()
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