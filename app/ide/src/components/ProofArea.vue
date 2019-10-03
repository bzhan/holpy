<template>
  <div>
    <label for="proof-area"></label>
    <textarea id="proof-area" class="proofArea"></textarea>
    <br>
    <div><pre>{{ status }}</pre></div>
    <div>
      <a href="#" id="link-backward" v-on:click="step_backward()">&lt;</a>
      <span id="instruction-number"> {{ instr_no }} </span>
      <a href="#" id="link-forward" v-on:click="step_forward()">&gt;</a>
      <span id="instruction" style="margin-left:10pt" v-html="instr"> </span>
    </div>
    <div class="thm-content">
      <pre v-for="(res,i) in search_res"
           :key="res.num"
           v-on:click="apply_thm_tactic(i)"
           v-html="highlight_html(res.display)"/> 
    </div>
  </div>
</template>

<script>
import 'codemirror/lib/codemirror.css'
import axios from 'axios'
import CodeMirror from 'codemirror'
import "./../../static/css/index.css"


export default {
  name: 'ProofArea',
  props: [
    'theory_name',
    'item'
  ],

  data: function () {
    return {
      editor: undefined,  // CodeMirror object
      edit_flag: false,   // Edit flag for CodeMirror
      instr: '',          // Display of current instruction
      status: '',         // Display of status (text)
      is_mousedown: false,  // Used to manage clicks
      search_res: [],     // List of search results
      method_sig: [],

      // Information about the proof
      index: 0,
      history: [],
      steps: [],
      goal: -1,
      facts: new Set(),
      vars: [],
      proof: undefined,
    }
  },

  computed: {
    instr_no: function () {
      if (this.history) {
        return this.index + '/' + (this.history.length - 1)
      } else {
        return ""
      }
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
      this.status = status
    },

    // Display selected facts (in yellow) and goal (in red).
    display_facts_and_goal: function () {
      let editor = this.editor
      editor.getAllMarks().forEach(e => {
          if (e.css === 'background: red' || e.css == 'background: yellow') {
              e.clear()
          }
      });
      if (this.goal !== -1) {
          let goal_line = editor.getLineHandle(this.goal).text;
          editor.markText({line: this.goal, ch: goal_line.length - 5},
                          {line: this.goal, ch: goal_line.length},
                          {css: 'background: red'});    
      }
      this.facts.forEach(fact_no => {
          let fact_line = editor.getLineHandle(fact_no).text;
          editor.markText({line: fact_no, ch: 0}, {line: fact_no, ch: fact_line.length},
                          {css: 'background: yellow'});
      })
    },

    display_checked_proof: function (result) {
      let editor = this.editor
      if ('failed' in result) {
        this.display_status(result.failed + ': ' + result.message, 'red')
      } else {
        this.proof = result.proof
        editor.startOperation()
        this.edit_flag = true
        this.display()
        this.edit_flag = false
        editor.endOperation()
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
          editor.setCursor(result.goal, 0)
          this.facts = []
          if ('facts' in result) {
            this.facts = result.facts
          }
        } else {
          var lineCount = editor.lineCount()
          var newLineNo = -1
          var preLineNo = 0
          if (this.goal !== -1) {
            preLineNo = this.goal
          }
          for (var i = preLineNo; i < lineCount; i++) {
            if (editor.getLine(i).indexOf('sorry') !== -1) {
              newLineNo = i
              break
            }
          }
          if (newLineNo === -1) {
            editor.setCursor(0, 0)
            this.facts = []
            this.goal = -1
          } else {
            editor.setCursor(newLineNo, 0)
            this.facts = []
            this.goal = newLineNo
          }
        }
        this.display_facts_and_goal()
        this.match_thm()
        editor.focus()
      }
    },

    rp: function (x) {
      if (x === 0) {
        return 'normal'
      } if (x === 1) {
        return 'bound'
      } if (x === 2) {
        return 'var'
      } if (x === 3) {
        return 'tvar'
      }
    },

    highlight_html: function (lst) {
      var output = ''
      for (let i = 0; i < lst.length; i++) {
        let val = lst[i]
        output = output + '<tt class="' + this.rp(val[1]) + '">' + val[0] + '</tt>'
      }
      return output
    },

    get_line_no_from_id: function (id, proof) {
      var found = -1;
      for (let i = 0; i < this.proof.length; i++) {
        if (this.proof[i].id === id)
          found = i;
      }
      return found;
    },

    display_instructions: function () {
      var hId = this.index
      this.instr = this.highlight_html(this.history[hId].steps_output)
      var proof_info = {
        proof: this.history[hId].proof,
        report: this.history[hId].report
      }
      if (hId < this.steps.length) {
        // Find line number corresponding to ids
        proof_info.goal = this.get_line_no_from_id(this.steps[hId].goal_id, proof_info.proof)
        proof_info.facts = []
        if (this.steps[hId].fact_ids !== undefined) {
          this.steps[hId].fact_ids.forEach(
            v => proof_info.facts.push(this.get_line_no_from_id(v, proof_info.proof))
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
        'goal_id': this.proof[goalNo].id,
        'fact_ids': factIds,
        'theory_name': 'hoare',
        'thm_name': undefined,
        'vars': this.vars,
        'proof': this.proof
      }
    },

    match_thm: async function () {
      var input = this.current_state()
      if (input === undefined) {
        this.search_res = []
      } else {
        let result = await axios({
          url: 'http://127.0.0.1:5000/api/search-method',
          method: 'POST',
          data: JSON.stringify(input)
        })

        this.search_res = result.data.search_res
      }
    },

    apply_thm_tactic: function (res_id) {
      var res = this.search_res[res_id];
      if (res === undefined)
          return;

      this.apply_method(res._method_name, res);
    },

    apply_method: function (methodName, args) {
      var count = 0
      var sigList = []
      var sigs = this.method_sig[methodName]
      var input = this.current_state()
      input.method_name = methodName
      if (args === undefined) {
        args = {}
      }
      sigs.forEach(function(sig, i) {
        if (sig in args) {
          input[sig] = args[sig]
        } else {
          sigList.push(sig)
          count += 1
        }
      })
      this.display_status('Running')
      this.apply_method_ajax(input)
    },

    apply_method_ajax: async function (input) {
      let result = await axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/apply-method',
        data: JSON.stringify(input)
      })

      if ('failed' in result.data) {
        this.display_status(result.data.failed + ': ' + result.data.message, 'red')
      } else {
        // Success
        var hId = this.index
        this.steps[hId] = input
        this.steps.length = hId + 1
        this.history[hId].steps_output = result.data.steps_output
        this.history[hId + 1] = {
          'steps_output': [['Current state', 0]],
          'proof': result.data.proof,
          'report': result.data.report
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

    display_have_prompt: function (editor, proof, lineNo, ch) {
      if (this.is_last_id(proof, lineNo)) {
        return this.display_str(editor, 'show ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
      } else {
        return this.display_str(editor, 'have ', lineNo, ch, {css: 'color: darkblue; font-weight: bold'})
      }
    },

    display_highlight_str: function (editor, p, lineNo, ch) {
      let color
      if (p[1] === 0) {
        color = 'color: black'
      } else if (p[1] === 1) {
        color = 'color: green'
      } else if (p[1] === 2) {
        color = 'color: blue'
      } else if (p[1] === 3) {
        color = 'color: purple'
      } else if (p[1] === 4) {
        color = 'color: silver'
      }
      return this.display_str(editor, p[0], lineNo, ch, {css: color})
    },

    display_highlight_strs: function (editor, ps, lineNo, ch) {
      for (let i = 0; i < ps.length; i++) {
        ch = this.display_highlight_str(editor, ps[i], lineNo, ch)
      }
      return ch
    },

    display_str: function (editor, str, lineNo, ch, mark) {
      let len = str.length
      editor.replaceRange(str, {line: lineNo, ch: ch}, {line: lineNo, ch: ch + len})
      if (typeof mark !== 'undefined') {
        editor.markText({line: lineNo, ch: ch}, {line: lineNo, ch: ch + len}, mark)
      }
      return ch + len
    },

    display_line: function (proof, lineNo) {
      let editor = this.editor
      let line = proof[lineNo]
      let ch = 0
      let strTemp = ''
      for (let i = 0; i < line.id.length; i++) {
        if (line.id[i] === '.') {
          strTemp += '  '
        }
      }
      ch = this.display_str(editor, strTemp, lineNo, ch, {css: 'font-weight: bold'})
      if (line.rule === 'assume') {
        ch = this.display_str(editor, 'assume ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
        ch = this.display_highlight_strs(editor, line.args_hl, lineNo, ch)
      } else if (line.rule === 'variable') {
        ch = this.display_str(editor, 'fix ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
        ch = this.display_highlight_strs(editor, line.args_hl, lineNo, ch)
      } else if (line.rule === 'subproof') {
        ch = this.display_have_prompt(editor, proof, lineNo, ch)
        ch = this.display_highlight_strs(editor, line.th_hl, lineNo, ch)
        ch = this.display_str(editor, ' with', lineNo, ch, {css: 'color: darkblue; font-weight: bold'})
      } else {
        // Display theorem with highlight
        if (line.th_hl.length > 0) {
          ch = this.display_have_prompt(editor, proof, lineNo, ch)
          ch = this.display_highlight_strs(editor, line.th_hl, lineNo, ch)
          ch = this.display_str(editor, ' by ', lineNo, ch, {css: 'font-weight: bold'})
        }
        // Display rule name
        ch = this.display_str(editor, line.rule, lineNo, ch)
        // Display args with highlight
        if (line.args_hl.length > 0) {
          ch = this.display_str(editor, ' ', lineNo, ch)
          ch = this.display_highlight_strs(editor, line.args_hl, lineNo, ch)
        }
        if (line.prevs.length > 0) {
          ch = this.display_str(editor, ' from ', lineNo, ch, {css: 'font-weight: bold'})
          ch = this.display_str(editor, line.prevs.join(', '), lineNo, ch)
        }
      }
      editor.execCommand('goDocEnd')
    },

    display: function () {
      if (this.editor) {
        let editor = this.editor
        let proof = this.proof
        editor.setValue('')
        editor.setOption('lineNumberFormatter', function(lineNo) {
          if (lineNo < proof.length) {
            return proof[lineNo].id
          } else {
            return ''
          }
        })
        let maxIdLen = 0
        for (let lineNo = 0; lineNo < this.proof.length; lineNo++) {
          let line = this.proof[lineNo];
          let idLen = line.id.length
          if (idLen >= maxIdLen) {
            maxIdLen = idLen
          }
          this.display_line(this.proof, lineNo)
          let len = editor.getLineHandle(lineNo).text.length
          editor.replaceRange('\n', {line: lineNo, ch: len}, {line: lineNo, ch: len + 1})
          if (line.rule === 'intros') {
            editor.markText({line: lineNo, ch: 0}, {line: lineNo}, {inclusiveRight: true, inclusiveLeft: true, collapsed: 'true'})
          }
        }
      }
    },

    // Select goal or fact
    mark_text: function () {
      let editor = this.editor;
      var line_num = editor.getCursor().line;
      var line = editor.getLineHandle(line_num).text;
      if (line_num >= this.proof.length) {
        return;
      }
      if (line.indexOf('sorry') !== -1) {
        // Choose a new goal
        this.goal = line_num;
      }
      else if (this.goal !== -1) {
        // Choose or unchoose a fact
        let i = this.facts.indexOf(line_num);
        if (i === -1)
          this.facts.push(line_num);
        else
          this.facts.splice(i, 1);
      }
      this.display_facts_and_goal();
    },

    init_proof: async function () {
      const data = {
        theory_name: this.theory_name,
        thm_name: this.item.name,
        item: this.item
      }
      console.log(data)

      let res = await axios.post('http://127.0.0.1:5000/api/init-empty-proof', JSON.stringify(data))
      console.log(res)
      
      this.goal = -1
      this.method_sig = res.data.method_sig
      this.vars = res.data.vars
      this.steps = []
      this.history = [{
        steps_output: [['Current state', 0]],
        proof: res.data.proof,
        report: res.data.report
      }]
      this.index = 0
      this.display_instructions()
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
    let editor = await CodeMirror.fromTextArea(document.getElementById("proof-area"), {
      mode: 'text/x-python',
      lineNumbers: true,
      firstLineNumber: 0,
      theme: '',
      lineWrapping: false,
      foldGutter: true,
      smartIndent: false,
      matchBrackets: true,
      viewportMargin: Infinity,
      gutters: ['CodeMirror-linenumbers', 'CodeMirror-foldgutter'],
      extraKeys: {
        'Ctrl-I': function () {
          this.apply_method('introduction')
        },
        'Ctrl-B': function () {
          this.apply_method('apply_backward_step')
        },
        'Ctrl-R': function () {
          this.apply_method('rewrite_goal')
        },
        'Ctrl-F': function () {
          this.apply_method('apply_forward_step')
        },
        'Ctrl-Q': function (cm) {
          cm.foldCode(cm.getCursor())
        }
      },
      beforeChange: function (cm, change) {
        if (!this.edit_flag) {
            change.cancel();
        }        
      }
    })

    let that = this
    editor.on('beforeChange', function (cm, change) {
      if (!that.edit_flag) {
        change.cancel();
      }
    });

    editor.on('cursorActivity', function (cm) {
      if (that.is_mousedown) {
        that.mark_text(cm);
        that.match_thm();
        that.is_mousedown = false;
      }
    });

    editor.on('mousedown', function (cm) {
      that.is_mousedown = true;
    });

    this.editor = editor
    this.init_proof()
  }
}

</script>

<style scoped>
  .proofArea {
    width: 100%;
    height: 2vh;
  }
</style>
