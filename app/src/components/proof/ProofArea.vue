<template>
  <div style="margin-top:8px">
    <div v-if="proof !== undefined">
      <ProofLine v-for="(line, index) in proof"
                 v-bind:key="index" v-bind:line="line"
                 v-bind:is_last_id="is_last_id(index)"
                 v-bind:is_goal="goal === index"
                 v-bind:is_fact="facts.indexOf(index) !== -1"
                 v-bind:can_select="can_select(goal, index)"
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
    'ref_context',
    'editor'
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

      // Maximum index in history that is read.
      max_loaded: -1,
    }
  },

  methods: {
    step_backward: function () {
      if (this.index > 0) {
        this.gotoStep(this.index - 1);
      }
    },

    step_forward: function () {
      if (this.index < this.history.length-1) {
        this.gotoStep(this.index + 1);
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

    compute_new_goal: function (start) {
      // Start search from the current goal, or the beginning
      // if there is no current goal.
      var pre_line_no = start
      var new_line_no = undefined
      for (var i = pre_line_no; i < this.proof.length; i++) {
        if (this.proof[i].rule === 'sorry') {
          new_line_no = i
          break
        }
      }
      if (new_line_no === undefined) {  // Past the last goal
        return -1
      } else {
        return new_line_no
      }
    },

    display_num_gaps: function () {
      if (this.num_gaps > 0) {
        this.display_status('OK. ' + this.num_gaps + ' gap(s) remaining.')
      } else {
        this.display_status('OK. Proof complete!')
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
      if (this.history[this.index] !== undefined) {
        if (this.index === this.history.length - 1) {
          this.ref_status.instr = [{text: "Current state", color: 0}]
        } else {
          this.ref_status.instr = this.history[this.index].steps_output
        }
        this.ref_status.instr_no = this.index + '/' + (this.history.length - 1)
      } else {
        this.ref_status.instr = ''
        this.ref_status.instr_no = ''
      }
    },

    display_history: function () {
      // Display history in ref_context
      var steps = []
      var h_len = this.history.length
      for (let i = 0; i < h_len-1; i++) {
        steps.push({
          error: this.history[i].error,
          steps_output: this.history[i].steps_output,
          is_read: this.max_loaded >= i
        })
      }
      steps.push({
        error: this.history[h_len-1].error,
        steps_output: [{text: "Current state", color: 0}],
        is_read: this.max_loaded >= h_len-1
      })
      this.ref_context.steps = steps
    },

    current_state: function () {
      if (this.goal === -1) {
        return undefined
      }
      var fact_ids = []
      for (let i = 0; i < this.facts.length; i++) {
        fact_ids.push(this.proof[this.facts[i]].id)
      }
      var goal_id = this.proof[this.goal].id

      return {
        username: this.$state.user,
        profile: this.editor.profile,
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        proof: {
          vars: this.vars,
          proof: this.proof,
        },
        step: {
          goal_id: goal_id,
          fact_ids: fact_ids,
        }
      }
    },

    match_thm: async function () {
      var input = this.current_state()
      if (input === undefined) {
        this.ref_status.search_res = []
        this.ref_context.ctxt = {}
      } else {
        var response = undefined
        try {
          response = await axios.post('http://127.0.0.1:5000/api/search-method', JSON.stringify(input))
        } catch (err) {
          this.$emit('set-message', {
            type: 'error',
            data: 'Server error'
          })
        }

        if (response === undefined) {
          this.display_status('Server error')
          this.ref_status.search_res = []
          this.ref_context.ctxt = []
        } else {
          this.ref_status.search_res = response.data.search_res
          this.ref_context.ctxt = response.data.ctxt
        }
      }
    },

    apply_thm_tactic: function (res_id) {
      var res = this.ref_status.search_res[res_id];
      if (res === undefined)
          return;

      this.apply_method(res.method_name, res);
    },

    // Apply method with the given method name, on the given
    // argments.
    apply_method: async function (method_name, args) {
      var sigs = this.method_sig[method_name]
      var input = this.current_state()
      input.step.method_name = method_name
      if (args === undefined) {
        args = {}
      }

      var sigList = []
      for (let i = 0; i < sigs.length; i++) {
        let sig = sigs[i]
        if (sig in args) {
          input.step[sig] = args[sig]
        } else {
          sigList.push(sig)
        }
      }

      if (sigList.length > 0) {
        let $vm = this
        const query_result = await new Promise(function (resolve, reject) {
          $vm.$emit('query', {
            title: 'Method ' + method_name,
            fields: sigList,
            resolve: resolve,
            reject: reject
          })
        })

      if (query_result !== undefined) {
          Object.assign(input.step, query_result)
          this.display_status('Running')
          this.apply_method_ajax(input)
        }
      } else {
        this.display_status('Running')
        this.apply_method_ajax(input)
      }
    },

    loadSteps: async function () {
      var result = undefined
      const at_end = (this.index === this.history.length-1)
      const input = {
        username: this.$state.user,
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        proof: {
          vars: this.vars,
          proof: this.history[this.max_loaded+1].proof
        },
        steps: this.steps.slice(this.max_loaded+1, at_end ? this.index : this.index+1)
      }
      try {
        result = await axios.post('http://127.0.0.1:5000/api/apply-steps', JSON.stringify(input))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }
      if (result === undefined) {
        this.display_status('Server error')
        return
      }

      const history = result.data.history
      const h_len = history.length
      for (let i = 0; i < h_len-1; i++) {
        this.history[this.max_loaded+i+1] = history[i]
      }
      const history_last = this.history[this.max_loaded+h_len]
      history_last.proof = history[h_len-1].proof
      history_last.num_gaps = history[h_len-1].num_gaps
      history_last.error = history[h_len-1].error
      this.max_loaded = this.index
    },

    // Go to the step given by index
    gotoStep: async function (index) {
      this.index = index
      if (this.index > this.max_loaded) {
        await this.loadSteps()
      }
      this.proof = this.history[index].proof
      this.num_gaps = this.history[index].num_gaps
      this.facts = []
      if (index === this.steps.length) {
        this.goal = this.compute_new_goal(0)
      } else {
        this.goal = this.get_line_no_from_id(this.steps[index].goal_id)
        const fact_ids = this.steps[index].fact_ids
        if (fact_ids !== undefined) {
          for (let i = 0; i < fact_ids.length; i++) {
            let fact_no = this.get_line_no_from_id(fact_ids[i])
            if (this.can_select(this.goal, fact_no)) {
              this.facts.push(fact_no)
            }
          }
        }
      }
      this.ref_context.selected_step = this.index
      this.display_history()
      this.display_num_gaps()
      this.display_instructions()
      this.match_thm()
    },

    // Delete the step given by index
    deleteStep: function (index) {
      this.history[index+1].proof = this.history[index].proof
      this.history.splice(index, 1)
      this.steps.splice(index, 1)
      this.max_loaded = index-1
      this.gotoStep(index)
    },

    apply_method_ajax: async function (input) {
      var result = undefined
      try {
        result = await axios.post('http://127.0.0.1:5000/api/apply-method', JSON.stringify(input))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }
      if (result === undefined) {
        this.display_status('Server error')
        return
      }

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
              input.step[k] = query_result[k]
            else
              input.step['param_' + k] = query_result[k]
          }
          this.apply_method_ajax(input)
        }
      } else if ('err_type' in result.data) {
        this.display_error(result.data.err_type, result.data.err_str, result.data.trace)
      } else {
        // Success
        var hId = this.index
        this.steps[hId] = input.step
        this.steps.length = hId + 1
        if (this.steps[hId].fact_ids.length === 0) {
          delete this.steps[hId].fact_ids
        }
        this.history[hId].steps_output = result.data.steps_output
        this.history[hId + 1] = {
          proof: result.data.proof,
          num_gaps: result.data.num_gaps
        }
        this.history.length = hId + 2
        this.max_loaded = hId + 1
        this.gotoStep(hId + 1)
      }
    },

    is_last_id: function (line_no) {
      if (this.proof.length - 1 === line_no) {
        return true
      }
      return this.proof[line_no + 1].rule === 'intros'
    },

    can_select: function (goal, line_no) {
      if (goal === -1)
        return false

      const goal_id = this.proof[goal].id.split('.')
      const fact_id = this.proof[line_no].id.split('.')
      const len = fact_id.length
      if (len > goal_id.length)
        return false
      for (let i = 0; i < len-1; i++)
        if (fact_id[i] !== goal_id[i])
          return false
      return Number(fact_id[len-1]) < Number(goal_id[len-1])
    },

    // Select goal or fact
    mark_text: function (line_no) {
      if (this.proof[line_no].rule === 'sorry') {
        // Choose a new goal
        this.goal = line_no;
      }
      else if (this.goal !== -1) {
        if (!this.can_select(this.goal, line_no)) {
          // Goal cannot depend on this fact
          return
        }
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
        username: this.$state.user,
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        proof: {
          vars: this.vars,
          prop: this.prop
        }
      }

      var response = undefined
      try {
        response = await axios.post('http://127.0.0.1:5000/api/init-empty-proof', JSON.stringify(data))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }
      if (response === undefined) {
        this.display_status('Server error')
        return
      }

      this.goal = -1
      this.method_sig = response.data.method_sig
      this.steps = []
      this.history = [{
        proof: response.data.proof,
        num_gaps: response.data.num_gaps
      }]
      this.gotoStep(0)
    },

    init_saved_proof: async function () {
      // Has existing proof
      const data = {
        username: this.$state.user,
        profile: this.editor !== undefined && this.editor.profile,
        theory_name: this.theory_name,
        thm_name: this.thm_name,
        proof: {
          vars: this.vars,
          prop: this.prop,
          steps: this.old_steps,
          proof: this.old_proof
        }
      }

      var response = undefined
      try {
        response = await axios.post('http://127.0.0.1:5000/api/init-saved-proof', JSON.stringify(data))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }
      if (response === undefined) {
        this.display_status('Server error')
        return
      }

      if ('err_type' in response.data) {
        this.display_error(response.data.err_type, response.data.err_str, response.data.trace)
      } else {
        this.method_sig = response.data.method_sig
        if (response.data.steps !== undefined) {
          // Case with history
          this.steps = response.data.steps
          this.history = response.data.history
          this.max_loaded = this.history.length-1
          this.gotoStep(this.history.length-1)
        } else {
          // Case without history
          this.num_gaps = response.data.num_gaps
          this.goal = -1
          this.facts = []
          this.proof = response.data.proof
          this.display_num_gaps()
          this.display_instructions()
          this.match_thm()
        }
      }
    },

    init_proof: async function () {
      if (this.old_proof === undefined) {
        this.init_empty_proof()
      } else {
        this.init_saved_proof()
      }
    },
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
