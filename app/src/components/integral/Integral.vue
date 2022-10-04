<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">Integral</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='load_file_list'>Open file</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Proof" left>
          <b-dropdown-item href="#" v-on:click="clearItem">Clear</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('FullSimplify')">Simplify</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addFuncDef">Add definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addGoal">Add goal</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="proofByCalculation">Proof by calculation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="proofByInduction">Proof by induction</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Limits" left>
          <b-dropdown-item href="#" v-on:click="applyRule('LHopital')">L'Hopital Rule</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Integral" left>
          <b-dropdown-item href="#" v-on:click="forwardSubstitution">Forward substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="backwardSubstitution">Backward substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="integrateByParts">Integrate by parts</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('ElimInfInterval')">Improper integral to limit</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('DerivIntExchange')">Exchange deriv and integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="elimAbs">Eliminate absolute value</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='splitRegion'>Splitting an Integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="solveEquation">Solve equation</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Rewrite" left>
          <b-dropdown-item href="#" v-on:click="expandDefinition">Expand definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="trigIdentity">Trig identities</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('ExpandPolynomial')">Expand polynomial</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('PolynomialDivision')">Polynomial division</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyTheorem">Apply theorem</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="rewriteEquation" id="rewriteEquation">Rewrite equation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyInductiveHyp">Apply inductive hyp.</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('RewriteFactorial')">Factorial</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="rewriteBinom">Binomial coefficients</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="rewriteLimit">Rewrite limit</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="rewriteExp">Rewrite exp</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="integrateBothSide0">Integrate both side</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <!-- Content of the file -->
    <div id="content">
      <div v-if="content_state === false" align=left>
        <div v-for="name in file_list" v-bind:key=name style="margin:5px 10px">
          <a href="#" v-on:click="openFile(name)">{{name}}</a>
        </div>
      </div>
      <div v-if="content_state === true">
        <div v-for="(item, index) in content" :key="index" style="margin:5px 10px">
          <div v-if="'type' in item && item.type == 'FuncDef'">
            <div class="math-text">Definition</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_eq + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Lemma'">
            <div class="math-text">Lemma</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_eq + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Goal'">
            <div class="math-text">Goal</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_goal + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Calculation'">
            <div class="math-text">Calculate</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_start + '\\)'"
              style="cursor:pointer"/>
          </div>
        </div>
      </div>
    </div>
    <!-- Main panel showing calculation -->
    <div v-if="cur_id !== undefined" id="problem">
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'FuncDef'">
        <FuncDef v-bind:item="content[cur_id]" v-bind:label="''"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Lemma'">
        <Lemma v-bind:item="content[cur_id]" v-bind:label="''"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Goal'">
        <Goal v-bind:item="content[cur_id]" v-bind:label="''"
          @select="selectItem"
          @select_fact="selectFact"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Calculation'">
        <Calculation v-bind:item="content[cur_id]" v-bind:label="''"
          @select="selectItem"
          @select_fact="selectFact"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
    </div>
    <div id="dialog">
      <div v-if="r_query_mode === 'add definition'">
        <span class="math-text">Add function definition:</span><br/>
        <ExprQuery v-model="expr_query1"/><br/>
        <div v-for="(cond, index) in cond_query" :key="index">
          <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)"/><br/>
        </div>
        <button v-on:click="doAddFuncDef">OK</button>&nbsp;
        <button v-on:click="cond_query.push('')">Add condition</button>
      </div>
      <div v-if="r_query_mode === 'add goal'">
        <span class="math-text">Add goal:</span><br/>
        <ExprQuery v-model="expr_query1"/><br/>
        <div v-for="(cond, index) in cond_query" :key="index">
          <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)"/><br/>
        </div>
        <button v-on:click="doAddGoal">OK</button>&nbsp;
        <button v-on:click="cond_query.push('')">Add condition</button>
      </div>
      <div v-if="r_query_mode === 'apply induction'">
        <span class="math-text">Please specify induction variable</span><br/>
        <input v-model="induct_var">
        <button v-on:click="doApplyInduction">OK</button>
      </div>
      <div v-if="r_query_mode === 'integrate by parts'">
        <span class="math-text">Integrate by parts on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[0].latex_body + '\\)'"/><br/>
        <MathEquation data="Choose \(u\) and \(v\) such that \(u\cdot\mathrm{d}v\) is the integrand."/>
        <div>
          <MathEquation data="\(u=\)"/>
          <ExprQuery v-model="expr_query1"/>
        </div>
        <div>
          <MathEquation data="\(v=\)"/>
          <ExprQuery v-model="expr_query2"/><br/>
        </div>
        <button v-on:click="doIntegrateByParts">OK</button>
      </div>
      <div v-if="r_query_mode === 'forward substitution'">
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_expr + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_int[int_id].loc}}</span><br/>
        <button v-bind:disabled='int_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='int_id == sep_int.length-1' v-on:click='int_id++'>next</button><br/>
        <span class="math-text">Substitution on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_body + '\\)'"/><br/>
        <span class="math-text">Substitute </span>
        <input v-model="subst_var"><br/>
        <span class="math-text"> for</span><br/>
        <ExprQuery v-model="expr_query1"/><br/>
        <button v-on:click="doForwardSubstitution">OK</button>

      </div>
      <div v-if="r_query_mode === 'backward substitution'">
        <span class="math-text">Backward substitution on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_body + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_int[int_id].loc}}</span><br/>
        <button v-bind:disabled='int_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='int_id == sep_int.length-1' v-on:click='int_id++'>next</button><br/>
        <span class="math-text">New variable </span>
        <input v-model="subst_var"><br/>
        <span class="math-text">Substitute </span>
        <span class="math-text-italic">{{sep_int[int_id].var_name}}</span>
        <span class="math-text"> for</span><br/>
        <ExprQuery v-model="expr_query1"/><br/>
        <button v-on:click="doBackwardSubstitution">OK</button>
      </div>
      <div v-if="r_query_mode === 'rewrite limit'">
        <span class="math-text">Rewrite limit on: </span>
        <MathEquation v-bind:data="'\\(' + sep_limit[limit_id].latex_expr + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_limit[limit_id].loc}}</span><br/>
        <button v-bind:disabled='limit_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='limit_id == sep_limit.length-1' v-on:click='limit_id++'>next</button><br/>
        <button v-on:click="doRewriteLimit">OK</button>
      </div>
      <div v-if="r_query_mode === 'elim abs'">
        <span class="math-text">Eliminate absolute value on: </span>
        <MathEquation v-bind:data="'\\(' + sep_abs[abs_id].latex_expr + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_abs[abs_id].loc}}</span><br/>
        <button v-bind:disabled='abs_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='abs_id == sep_abs.length-1' v-on:click='abs_id++'>next</button><br/>
        <button v-on:click="doElimAbs">OK</button>
      </div>
      <div v-if="r_query_mode === 'trig identity'">
        <div class="math-text">Select subexpression:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
             @select="selectExpr"><br/>
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/>
        <div v-for="(item, index) in trig_rewrites" :key="index"
             v-on:click="doTrigIdentity(index)">
          <MathEquation v-bind:data="'\\(=' + item.latex_new_e + '\\)'" style="cursor:pointer"/>
        </div>
      </div>
      <div v-if="r_query_mode === 'rewrite equation'">
        <div class="math-text">Select subexpression:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
             @select="selectExpr"><br/>
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <span class="math-text">Rewrite subexpression to</span><br/>
        <ExprQuery v-model="expr_query1"/>
        <button v-on:click="doRewriteEquation">OK</button>
      </div>
      <div v-if="r_query_mode === 'split region'">
        <div class="math-text">Split region at:</div>
        <ExprQuery v-model="expr_query1"/>
        <button v-on:click="doSplitRegion">OK</button>
      </div>
      <div v-if="r_query_mode === 'select theorem'">
        <div class="math-text">Select theorem to apply:</div>
        <div v-for="(item, index) in theorems" :key="index"
             v-on:click="doApplyTheorem(index)" style="cursor:pointer">
          <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'"/>
        </div>
      </div>
      <div v-if="r_query_mode === 'query vars'">
        <div class="math-text">Enter instantiation in theorem</div>
        <MathEquation v-bind:data="'\\(' + theorems[selected_theorem_id].latex_eq + '\\)'"/><br/>
        <div v-for="(item, index) in query_vars" :key="index">
          <MathEquation v-bind:data="'\\(' + item.var + '\\to \\)'"/>
          <ExprQuery v-model="item.expr"/>
        </div>
        <button v-on:click="doApplyTheoremInst">OK</button>
      </div>
      <div v-if="r_query_mode === 'rewrite binom'">
        <span class="math-text">Rewrite binomial coffcient: </span>
        <MathEquation v-bind:data="'\\(' + sep_binom[binom_id].latex_expr + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_binom[binom_id].loc}}</span><br/>
        <button v-bind:disabled='binom_id == 0' v-on:click="binom_id--">prev</button>
        <button v-bind:disabled='binom_id == sep_binom.length-1' v-on:click='binom_id++'>next</button><br/>
        <button v-on:click="doRewriteBinom">OK</button>
      </div>
      <div v-if="r_query_mode === 'rewrite exp'">
        <span class="math-text">Rewrite exp on: </span>
        <MathEquation v-bind:data="'\\(' + sep_exp[exp_id].latex_expr + '\\)'"/><br/>
        <span class="math-text">Location: {{sep_exp[exp_id].loc}}</span><br/>
        <button v-bind:disabled='exp_id == 0' v-on:click="exp_id--">prev</button>
        <button v-bind:disabled='exp_id == sep_exp.length-1' v-on:click='exp_id++'>next</button><br/>
        <button v-on:click="doRewriteExp">OK</button>
      </div> 
      <div v-if="r_query_mode === 'integrate both side0'">
        <span class="math-text">Integrate both side on: </span>
        <MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'"/><br/>
        <span class="math-text">Integral variable:</span><input v-model="integral_var"><br/>
        <button v-on:click="integrateBothSide1">OK</button>
      </div> 
      <div v-if="r_query_mode === 'integrate both side1'">
        <span class="math-text">Integrate both side on: </span>
        <MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'"/><br/>
        <div v-if="left_skolem === true"><span class="math-text">Left skolem const name:</span><input v-model="left_skolem_name"><br/></div>
        <div v-if="right_skolem === true"><span class="math-text">Right skolem const name:</span><input v-model="right_skolem_name"><br/></div>
        <button v-on:click="doIntegrateBothSide">OK</button>
      </div> 
    </div>
    <div id="select">
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import MathEquation from '../util/MathEquation.vue'
import FuncDef from './FuncDef.vue'
import ExprQuery from './ExprQuery.vue'
import Goal from "./Goal.vue"
import Lemma from "./Lemma.vue"
import Calculation from "./Calculation.vue"

export default {
  name: 'Integral',
  components: {
    MathEquation,
    FuncDef,
    Goal,
    Calculation,
    ExprQuery,
    Lemma,
  },

  props: [
  ],

  data: function () {
    return {
      filename: 'tongji7',       // Currently opened file
      content: [],               // List of problems
      file_list: [],             // List of integral list
      content_state: undefined,  // Display items in content or json files in file list
      cur_id: undefined,         // ID of the selected item
      cur_items: [],             // Current items in state
      r_query_mode: undefined,   // Record query mode
      sep_int: [],               // All separate integrals
      sep_binom: [],             // All binomial coeffcients
      sep_limit: [],             // All limits
      sep_abs: [],               // all integrals of abs function and abs expressions
      sep_exp: [],               // all exponetial expressions

      // Selected goal
      selected_item: undefined,

      // Query for expressions
      expr_query1: undefined,
      expr_query2: undefined,

      // Query for conditions
      cond_query: [],

      // Query for substitution variable
      subst_var: undefined,

      // Query for induction variable
      induct_var: undefined,

      // Selected fact
      selected_facts: {},

      // Selected latex expression
      selected_expr: undefined,
      latex_selected_expr: undefined,
      trig_rewrites: undefined,

      // List of theorems
      theorems: undefined,
      selected_theorem_id: undefined,
      query_vars: undefined,

      // the choosed step expression
      last_expr: undefined,
			
      // the index of sep-integrals
      int_id: 0,

      // the index of sep-binoms
      binom_id: 0,

      // the index of sep-limits
      limit_id: 0,

      //the index of sep-abs
      abs_id: 0,

      //the index of sep-exp
      exp_id: 0,

      integral_var: undefined,
      left_skolem: false,
      right_skolem: false,
      left_skolem_name: undefined,
      right_skolem_name: undefined,
    }
  },

  computed: {
    lastExpr: function() {
      this.query_last_expr()
      return this.last_expr
    }
  },

  methods: {
    query_last_expr: async function(){
        const data = {
          item: this.content[this.cur_id],
          selected_item: this.selected_item
        }
        const response = await axios.post("http://127.0.0.1:5000/api/query-last-expr", JSON.stringify(data))
        if (response.data.status === 'ok'){
          this.last_expr = response.data.last_expr
        } else {
          this.last_expr = ""
        }
    },
		
    load_file_list: async function (){
      const response = await axios.post('http://127.0.0.1:5000/api/integral-load-file-list')
      this.file_list = response.data.file_list
      this.content_state = false
      this.content = []
      this.cur_id = undefined
      this.cur_items = undefined
    },

    openFile: async function (file_name) {
      const data = {
        filename: file_name
      };
      this.filename = file_name
      const response = await axios.post("http://127.0.0.1:5000/api/integral-open-file", JSON.stringify(data))
      this.content = response.data.content
      this.cur_id = undefined
      this.cur_items = undefined
      this.content_state = true
    },

    initialize: async function (index) {
      this.r_query_mode = undefined
      this.cur_id = index
      this.selected_item = undefined
      this.selected_facts = {}
    },

    // Select an item
    selectItem: function(item_id) {
      console.log('selectItem', item_id)
      this.selected_item = item_id
      this.r_query_mode = undefined
    },

    // Select a fact
    selectFact: function(item_id) {
      console.log('selectFact', item_id)
      if (item_id in this.selected_facts) {
        this.$delete(this.selected_facts, item_id)
      } else {
        this.$set(this.selected_facts, item_id, true)
      }
    },

    // Restart proof, delete all steps
    clearItem: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item
      }
      if (this.selected_item === undefined) {
        data.selected_item = ""
      }
      const response = await axios.post("http://127.0.0.1:5000/api/clear-item", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        if ('selected_item' in response.data) {
          this.selected_item = response.data.selected_item
        }
      }
    },

    setCondQuery: function(index, value) {
      this.$set(this.cond_query, index, value)
    },

    // Add function definition
    addFuncDef: function() {
      this.r_query_mode = 'add definition'
    },

    // Perform add function definition
    doAddFuncDef: async function() {
      const data = {
        name: this.content[this.cur_id].name,
        problem: this.content[this.cur_id].problem,
        items: this.cur_items,
        eq: this.expr_query1,
        conds: this.cond_query
      }
      const response = await axios.post("http://127.0.0.1:5000/api/add-function-definition", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.cur_items = response.data.state.items
        this.r_query_mode = undefined
        this.expr_query1 = ''
        this.cond_query = []
      }
    },

    // Add goal
    addGoal: function() {
      this.r_query_mode = 'add goal'
    },

    // Perform add goal
    doAddGoal: async function() {
      const data = {
        name: this.content[this.cur_id].name,
        problem: this.content[this.cur_id].problem,
        items: this.cur_items,
        goal: this.expr_query1,
        conds: this.cond_query
      }
      const response = await axios.post("http://127.0.0.1:5000/api/add-goal", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.cur_items = response.data.state.items
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
        this.expr_query1 = ''
        this.cond_query = []
      }
    },

    // Perform proof by calculation
    proofByCalculation: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/proof-by-calculation", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // Proof by induction
    proofByInduction: function() {
      this.r_query_mode = 'apply induction'
    },

    applyRule: async function(rulename) {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: rulename
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // Perform proof by induction
    doApplyInduction: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        induct_var: this.induct_var
      }
      const response = await axios.post("http://127.0.0.1:5000/api/proof-by-induction", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // Expand definition
    expandDefinition: async function() {
      const data = {
        item: this.content[this.cur_id],
        prev_items: this.content.slice(0, this.cur_id),
        selected_item: this.selected_item,
      }
      console.log(this.content[this.cur_id])
      console.log(this.content.slice(0, this.cur_id))
      console.log(this.selected_item)
      const response = await axios.post("http://127.0.0.1:5000/api/expand-definition", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    integrateByParts: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.r_query_mode = 'integrate by parts'
      }
    },

    trigIdentity: function() {
      this.r_query_mode = 'trig identity'
    },

    selectExpr: async function() {
      const start = this.$refs.select_expr1.selectionStart
      const end = this.$refs.select_expr1.selectionEnd
      this.selected_expr = this.lastExpr.slice(start, end)   
      const data = {
        expr: this.selected_expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-trig-identity", JSON.stringify(data))
      if (response.data.status === 'ok') {
        this.latex_selected_expr = response.data.latex_expr
        this.trig_rewrites = response.data.results
      } else {
        this.trig_rewrites = undefined
      }
    },

    doTrigIdentity: async function(index) {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: "RewriteTrigonometric",
          rule_name: this.trig_rewrites[index].rule_name,
          rewrite_term: this.selected_expr
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    doIntegrateByParts: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: "IntegrationByParts",
          u: this.expr_query1,
          v: this.expr_query2
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    forwardSubstitution: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.r_query_mode = 'forward substitution'
      }
    },

    doForwardSubstitution: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'Substitution',
          var_name: this.subst_var,
          var_subst: this.expr_query1,
          loc: this.sep_int[this.int_id].loc,
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    backwardSubstitution: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.int_id = 0
        this.r_query_mode = 'backward substitution'
      }
    },
    
    doBackwardSubstitution: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'SubstitutionInverse',
          var_name: this.subst_var,
          var_subst: this.expr_query1,
          loc: this.sep_int[this.int_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    rewriteLimit: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-limit", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_limit = response.data.limits
        this.limit_id = 0
        if (response.data.limits.length == 1){
          this.doRewriteLimit()
        } else {
          this.r_query_mode = 'rewrite limit'
        }
      }
    },

    doRewriteLimit: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'RewriteLimit',
          loc: this.sep_limit[this.limit_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    solveEquation: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        selected_facts: this.selected_facts
      }
      const response = await axios.post("http://127.0.0.1:5000/api/solve-equation", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
        this.selected_facts = {}
      }
    },

    rewriteEquation: function() {
      this.r_query_mode = 'rewrite equation'
    },

    doRewriteEquation: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: "Equation",
          old_expr: this.selected_expr,
          new_expr: this.expr_query1
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    splitRegion: function() {
      this.r_query_mode = 'split region'
    },

    doSplitRegion: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: "SplitRegion",
          c: this.expr_query1
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    applyTheorem: async function() {
      const data = {
        item: this.content[this.cur_id],
        prev_items: this.content.slice(0, this.cur_id),
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-theorems", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.theorems = response.data.theorems
        this.r_query_mode = 'select theorem'
      }
    },

    doApplyTheorem: async function(index) {
      this.selected_theorem_id = index
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        theorem: this.theorems[index].eq
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-apply-theorem", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      } else if (response.data.status == 'query') {
        this.query_vars = response.data.query_vars
        this.r_query_mode = 'query vars'
      }
    },

    doApplyTheoremInst: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: "ApplyEquation",
          eq: this.theorems[this.selected_theorem_id].eq,
          subMap: this.query_vars
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    applyInductiveHyp: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }      
      const response = await axios.post("http://127.0.0.1:5000/api/apply-inductive-hyp", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    rewriteBinom: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-binom", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_binom = response.data.binoms
        this.binom_id = 0
        this.r_query_mode = 'rewrite binom'
      }
    },
    
    doRewriteBinom: async function() {
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'RewriteBinom',
          loc: this.sep_binom[this.binom_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    elimAbs: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-abs", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_abs = response.data.abs_exprs
        this.abs_id = 0
        if (response.data.abs_exprs.length == 1){
          this.doElimAbs()
        } else {
          this.r_query_mode = 'elim abs'
        }
      }
    },

    doElimAbs: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'ElimAbs',
          loc: this.sep_abs[this.abs_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    rewriteExp: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-exp", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_exp = response.data.exps
        this.exp_id = 0
        if (response.data.exps.length == 1){
          this.doRewriteExp()
        } else {
          this.r_query_mode = 'rewrite exp'
        }
      }
    },

    doRewriteExp: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'RewriteExp',
          loc: this.sep_exp[this.exp_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    integrateBothSide0: async function(){
      console.log("integrate both side0")
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-last-expr", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.latex_selected_expr = response.data.latex_expr
        this.r_query_mode = 'integrate both side0'
      }
    },

    integrateBothSide1: async function(){
      console.log("integrate both side1")
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        integral_var: this.integral_var,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integrate-both-side", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.left_skolem = response.data.left_skolem
        this.right_skolem = response.data.right_skolem
        this.r_query_mode = 'integrate both side1'
      }
    },

    doIntegrateBothSide: async function(){
      const data = {
        item: this.content[this.cur_id],
        selected_item: this.selected_item,
        rule: {
          name: 'IntegrateBothSide',
          integral_var: this.integral_var,
          left_skolem: this.left_skolem,
          right_skolem: this.right_skolem,
          left_skolem_name: this.left_skolem_name,
          right_skolem_name: this.right_skolem_name,
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
        this.integral_var = undefined
        this.left_skolem = false
        this.right_skolem = false
        this.left_skolem_name = undefined
        this.right_skolem_name = undefined

      }
    },
    // doRewriteEquation: async function() {
    //   const data = {
    //     item: this.content[this.cur_id],
    //     selected_item: this.selected_item,
    //     rule: {
    //       name: "Equation",
    //       old_expr: this.selected_expr,
    //       new_expr: this.expr_query1
    //     }
    //   }
    //   const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
    //   if (response.data.status == 'ok') {
    //     this.$set(this.content, this.cur_id, response.data.item)
    //     this.selected_item = response.data.selected_item
    //     this.r_query_mode = undefined
    //   }
    // },
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
  font-size: large;
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

#items {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
  font-size: 20px;
}

#problem {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
  font-size: 20px;
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
.MathJax_Display {
  color: rgb(255, 255, 255) !important;
}

</style>