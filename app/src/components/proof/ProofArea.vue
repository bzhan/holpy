<template>
  <div style="margin-top:8px">
    <div v-if="proof !== undefined">
      <ProofLine v-for="(line, index) in proof"
                 v-bind:key="index" v-bind:line="line"
                 v-bind:is_last_id="is_last_id(proof, index)"
                 v-bind:is_goal="goal === index"
                 v-bind:is_fact="facts.indexOf(index) !== -1"
                 v-on:select="mark_text(index)"/>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import ProofLine from './ProofLine'

export default {
  name: 'ProofArea',

  components: {
    ProofLine,
  },

  props: [
    // Input theory_name and thm_name specifies the position in the
    // library at which the proof is carried out. All definitions
    // and theorems up to the given theory and up to (but not including)
    // the given theorem may be used in the proof.
    //
    // For example, if proving a theorem in the library, these should
    // be the name of the theory the theorem is in, and the name of the
    // theorem itself.
    //
    // If proving something depending on certain theory, these should
    // be name of the theory and undefined (for requiring everything in
    // the theory).
    'theory_name', 'thm_name',

    // Dictionary specifying variables. 
    'vars',

    // Statement of the theorem to be proved.
    'prop',

    // Initial value for steps and proof
    'old_steps',
    'old_proof',

    // Area for displaying status and context
    'ref_status',
    'ref_context'
  ],

  data: function () {
    return {
      // Method signature
      method_sig: [],

      // Information about the proof
      index: 0,
      history: [],
      steps: [],
      goal: -1,
      facts: new Set(),
      proof: undefined,
    }
  },

  methods: {
    step_backward: function () {
      if (this.index > 0) {
        this.index--;
        this.display_instructions();
      }
    },

    step_forward: function () {
      if (this.index < this.history.length-1) {
        this.index++;
        this.display_instructions();
      }
    },

    display_status: function (status) {
      this.ref_status.status = status
      this.ref_status.trace = undefined
    },

    display_error: function (err_type, err_str, trace) {
      this.ref_status.status = err_type + ": " + err_str
      this.ref_status.trace = trace
    },

    display_checked_proof: function (result) {
      if ('err_type' in result) {
        this.display_error(result.err_type, result.err_str, result.trace)
      } else {
        this.proof = result.proof
        var numGaps = result.report.num_gaps
        this.num_gaps = numGaps
        if (numGaps > 0) {
          this.display_status('OK. ' + numGaps + ' gap(s) remaining.')
        } else {
          this.display_status('OK. Proof complete!')
        }

        if ('goal' in result) {
          // Looking at a previous step, already has goal_id and fact_id
          this.goal = result.goal
          this.facts = []
          if ('facts' in result) {
            this.facts = result.facts
          }
        } else {
          var newLineNo = -1
          var preLineNo = 0
          if (this.goal !== -1) {
            preLineNo = this.goal
          }
          for (var i = preLineNo; i < this.proof.length; i++) {
            if (this.proof[i].rule === 'sorry') {
              newLineNo = i
              break
            }
          }
          if (newLineNo === -1) {
            this.facts = []
            this.goal = -1
          } else {
            this.facts = []
            this.goal = newLineNo
          }
        }
        this.match_thm()
      }
    },

    get_line_no_from_id: function (id) {
      var found = -1;
      for (let i = 0; i < this.proof.length; i++) {
        if (this.proof[i].id === id)
          found = i;
      }
      return found;
    },

    display_instructions: function () {
      var hId = this.index
      this.ref_status.instr = this.history[hId].steps_output
      this.ref_status.instr_no = this.index + '/' + (this.history.length - 1)

      var proof_info = {
        proof: this.history[hId].proof,
        report: this.history[hId].report
      }
      if (hId < this.steps.length) {
        // Find line number corresponding to ids
        proof_info.goal = this.get_line_no_from_id(this.steps[hId].goal_id)
        proof_info.facts = []
        if (this.steps[hId].fact_ids !== undefined) {
          this.steps[hId].fact_ids.forEach(
            v => proof_info.facts.push(this.get_line_no_from_id(v))
          )
        }
      }
      this.display_checked_proof(proof_info)
    },

    current_state: function () {
      var goalNo = this.goal
      if (goalNo === -1) {
        return undefined
      }
      var factIds = []
      this.facts.forEach(v => factIds.push(this.proof[v].id))
      return {
        goal_id: this.proof[goalNo].id,
        fact_ids: factIds,
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        vars: this.vars,
        proof: this.proof
      }
    },

    match_thm: async function () {
      var input = this.current_state()
      if (input === undefined) {
        this.ref_status.search_res = []
        this.ref_context.ctxt = {}
      } else {
        let response = await axios.post('http://127.0.0.1:5000/api/search-method', JSON.stringify(input))

        this.ref_status.search_res = response.data.search_res
        this.ref_context.ctxt = response.data.ctxt
      }
    },

    apply_thm_tactic: function (res_id) {
      var res = this.ref_status.search_res[res_id];
      if (res === undefined)
          return;

      this.apply_method(res._method_name, res);
    },

    apply_method: async function (methodName, args) {
      var count = 0
      var sigList = []
      var sigs = this.method_sig[methodName]
      var input = this.current_state()
      input.method_name = methodName
      if (args === undefined) {
        args = {}
      }
      for (let i = 0; i < sigs.length; i++) {
        let sig = sigs[i]
        if (sig in args) {
          input[sig] = args[sig]
        } else {
          sigList.push(sig)
          count += 1
        }
      }

      if (count > 0) {
        let $vm = this
        const query_result = await new Promise(function (resolve, reject) {
          $vm.$emit('query', {
            title: 'Method ' + methodName,
            fields: sigList,
            resolve: resolve,
            reject: reject
          })
        })

      if (query_result !== undefined) {
          Object.assign(input, query_result)
          this.display_status('Running')
          this.apply_method_ajax(input)
        }
      } else {
        this.display_status('Running')
        this.apply_method_ajax(input)
      }
    },

    apply_method_ajax: async function (input) {
      const result = await axios.post('http://127.0.0.1:5000/api/apply-method', JSON.stringify(input))

      if ('query' in result.data) {
        let $vm = this
        const query_result = await new Promise(function (resolve, reject) {
          $vm.$emit('query', {
            title: 'Query for parameters',
            fields: result.data.query.map(s => s === 'names' ? s : s.slice(6)), // get rid of 'param_'
            resolve: resolve,
            reject: reject
          })
        })

        if (query_result !== undefined) {
          for (var k in query_result) {
            if (k === 'names')
              input[k] = query_result[k]
            else
              input['param_' + k] = query_result[k]
          }
          this.apply_method_ajax(input)
        }
      } else if ('err_type' in result.data) {
        this.display_error(result.data.err_type, result.data.err_str, result.data.trace)
      } else {
        // Success
        var hId = this.index
        this.steps[hId] = input
        this.steps.length = hId + 1
        this.history[hId].steps_output = result.data.steps_output
        this.history[hId + 1] = {
          steps_output: [['Current state', 0]],
          proof: result.data.proof,
          report: result.data.report
        }
        this.history.length = hId + 2
        if (input.fact_ids.length === 0) { delete input.fact_ids }
        delete input.theory_name
        delete input.thm_name
        delete input.vars
        delete input.proof
        this.index += 1
        this.display_instructions()
      }
    },

    is_last_id: function (proof, lineNo) {
      if (proof.length - 1 === lineNo) {
        return true
      }
      return proof[lineNo + 1].rule === 'intros'
    },

    // Select goal or fact
    mark_text: function (line_no) {
      if (this.proof[line_no].rule === 'sorry') {
        // Choose a new goal
        this.goal = line_no;
      }
      else if (this.goal !== -1) {
        // Choose or unchoose a fact
        let i = this.facts.indexOf(line_no);
        if (i === -1)
          this.facts.push(line_no);
        else
          this.facts.splice(i, 1);
      }
      this.match_thm();
    },

    init_empty_proof: async function () {
      // Start new proof
      const data = {
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        vars: this.vars,
        prop: this.prop
      }

      let response = await axios.post('http://127.0.0.1:5000/api/init-empty-proof', JSON.stringify(data))

      this.goal = -1
      this.method_sig = response.data.method_sig
      this.steps = []
      this.history = [{
        steps_output: [['Current state', 0]],
        proof: response.data.proof,
        report: response.data.report
      }]
      this.index = 0
      this.display_instructions()
    },

    init_saved_proof: async function () {
      // Has existing proof
      const data = {
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        vars: this.vars,
        prop: this.prop,
        steps: this.old_steps,
        proof: this.old_proof
      }

      let response = await axios.post('http://127.0.0.1:5000/api/init-saved-proof', JSON.stringify(data))

      if ('err_type' in response.data) {
        this.display_error(response.data.err_type, response.data.err_str, response.data.trace)
      } else {
        this.goal = -1
        this.method_sig = response.data.method_sig
        this.steps = response.data.steps
        if (response.data.history !== undefined) {
          this.history = response.data.history
          this.index = response.data.history.length - 1
          this.display_instructions()
        } else {
          this.proof = response.data.proof
          this.display_checked_proof(response.data)
        }
      }
    },

    init_proof: async function () {
      if (this.old_steps === undefined) {
        this.init_empty_proof()
      } else {
        this.init_saved_proof()
      }
    },

    undo_move: function () {
      var h_id = this.index;
      if (h_id < this.steps.length) {
          // Perform undo only when at end
          return;
      }

      this.history.length -= 1;
      this.history[h_id-1].steps_output = [["Current state", 0]]
      this.index = h_id - 1;
      this.display_instructions();

      // Remove last step after display_instructions, so goal and fact_no can
      // be used during display.
      this.steps.length -= 1;
    }
  },

  async mounted() {
    if (this.prop) {
      this.init_proof()
    }
  },

  watch: {
    prop: function () {
      this.init_proof()
    }
  },
}

</script>
