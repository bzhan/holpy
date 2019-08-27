<template>
  <div class="tab-pane fade active code-cell">
    <label :for=page_num></label>
    <textarea :id=page_num v-model="proof" class="proofArea"></textarea>
    <br>
    <info :status="status" :color="color" :instr_no="cell.index + '/' + (cell.history.length - 1)" :instr="instr" ref="info"/>
  </div>
</template>

<script>
import 'codemirror/lib/codemirror.css'
import info from '@/components/Info'
import axios from 'axios'
let CodeMirror = require('codemirror/lib/codemirror')

export default {
  name: 'proofArea',
  props: ['page_num', 'proof'],
  components: [info],
  data: function () {
    return {
      editor: '',
      textId: 0,
      cell: {},
      instr: '',
      edit_flag: false,
      status: '',
      color: ''
    }
  },
  methods: {
    display_status: function(status, color = '') {
      this.status = status
      this.color = color
    },
    display_checked_proof: function(result) {
      var cell = this.cell
      if ('failed' in result) {
        this.display_status(result.failed + ': ' + result.message, 'red')
      } else {
        cell.proof = result.proof
        var editor = this.get_selected_editor()
        editor.startOperation()
        this.edit_flag = true
        this.display(id)
        this.edit_flag = false
        editor.endOperation()
        var numGaps = result.report.num_gaps
        cell.num_gaps = numGaps
        if (numGaps > 0) {
          this.display_status('OK. ' + numGaps + ' gap(s) remaining.')
        } else {
          this.display_status('OK. Proof complete!')
        }

        if ('goal' in result) {
          // Looking at a previous step, already has goal_id and fact_id
          cell.goal = result.goal
          editor.setCursor(result.goal, 0)
          cell.facts = []
          if ('facts' in result) {
            cell.facts = result.facts
          }
        } else {
          var lineCount = editor.lineCount()
          var newLineNo = -1
          var preLineNo = 0
          if (cell.goal !== -1) { preLineNo = cell.goal }
          for (var i = preLineNo; i < lineCount; i++) {
            if (editor.getLine(i).indexOf('sorry') !== -1) {
              newLineNo = i
              break
            }
          }
          if (newLineNo === -1) {
            editor.setCursor(0, 0)
            cell.facts = []
            cell.goal = -1
          } else {
            editor.setCursor(newLineNo, 0)
            cell.facts = []
            cell.goal = newLineNo
          }
        }
        this.display_facts_and_goal(editor)
        this.match_thm()
        editor.focus()
      }
    },
    rp: function(x) {
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
    highlight_html: function(lst) {
      var output = ''
      lst.forEach(function (val, i) {
        output = output + '<tt class="' + this.rp(val[1]) + '">' + val[0] + '</tt>'
      })
      return output
    },
    display_instructions: function() {
      var id = this.get_selected_id()
      var hId = cell.index
      var templ_instr = _.template($('#template-instruction').html())
      $('.rbottom .selected div#output-instr').html(templ_instr({
        instr_no: hId + '/' + (cell.history.length - 1),
        instr: this.highlight_html(cell.history[hId].steps_output)
      }))
      this.instr = this.highlight_html(cell.history[hId].steps_output)
      var proofInfo = {
        proof: cell.history[hId].proof,
        report: cell.history[hId].report
      }
      if (hId < cell.steps.length) {
        // Find line number corresponding to ids
        proofInfo.goal = get_line_no_from_id(cell.steps[hId].goal_id, proof_info.proof)
        proofInfo.facts = []
        if (cell.steps[hId].fact_ids !== undefined) {
          cell.steps[hId].fact_ids.forEach(
            v => proofInfo.facts.push(get_line_no_from_id(v, proof_info.proof))
          )
        }
      }
      this.display_checked_proof(proofInfo)
    },
    current_state: function() {
      var goalNo = this.cell.goal
      if (goalNo === -1) {
        return undefined
      }
      var factIds = []
      this.cell.facts.forEach(v => factIds.push(this.cell.proof[v].id))
      return {
        'id': id,
        'goal_id': this.cell.proof[goalNo].id,
        'fact_ids': factIds,
        'theory_name': this.cell.theory_name,
        'thm_name': this.cell.thm_name,
        'vars': this.cell.vars,
        'proof': this.cell.proof
      }
    },
    match_thm: function(cell) {
      var input = this.current_state()
      if (input === undefined) {
        cell.search_res = []
        this.display_match_thm()
      } else {
        axios({
          url: '/api/search-method',
          type: 'POST',
          data: JSON.stringify(input),
          success: function (result) {
            cell.search_res = result.search_res
            this.display_match_thm()
          }
        })
      }
    },
    apply_method: function(methodName, args) {
      var count = 0
      var cell = this.cell
      var sigList = []
      var sigs = cell.method_sig[methodName]
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
      this.display_running()
      this.apply_method_ajax(input)
    },
    apply_method_ajax: function (input) {
      var cell = this.cell
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/apply-method',
        data: JSON.stringify(input),
        success: function(result) {
          if ('failed' in result) {
            this.display_status(result.failed + ': ' + result.message, 'red')
          } else {
            // Success
            var id = input.id
            var hId = cell.index
            cell.steps[hId] = input
            cell.steps.length = hId + 1
            cell.history[hId].steps_output = result.steps_output
            cell.history[hId + 1] = {
              'steps_output': [['Current state', 0]],
              'proof': result.proof,
              'report': result.report
            }
            cell.history.length = hId + 2
            delete input.id
            if (input.fact_ids.length === 0) { delete input.fact_ids }
            delete input.theory_name
            delete input.thm_name
            delete input.vars
            delete input.proof
            cell.index += 1
            this.display_instructions()
          }
        }
      })
    },
    is_last_id(proof, lineNo) {
      if (proof.length - 1 === lineNo) {
        return true
      }
      return proof[lineNo + 1].rule === 'intros'
    },
    display_have_prompt(editor, proof, lineNo, ch, that) {
      if (that.is_last_id(proof, lineNo)) {
        return that.display_str(editor, 'show ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
      } else {
        return that.display_str(editor, 'have ', lineNo, ch, {css: 'color: darkblue; font-weight: bold'})
      }
    },
    display_highlight_str(editor, p, lineNo, ch, that) {
      let color
      if (p[1] === 0) { color = 'color: black' } else if (p[1] === 1) { color = 'color: green' } else if (p[1] === 2) { color = 'color: blue' } else if (p[1] === 3) { color = 'color: purple' } else if (p[1] === 4) { color = 'color: silver' }
      return that.display_str(editor, p[0], lineNo, ch, {css: color})
    },
    display_highlight_strs(editor, ps, lineNo, ch, that) {
      for (let i = 0; i < ps.length; i++) {
        ch = that.display_highlight_str(editor, ps[i], lineNo, ch, that)
      }
      return ch
    },
    display_str(editor, str, lineNo, ch, mark) {
      let len = str.length
      editor.replaceRange(str, {line: lineNo, ch: ch}, {line: lineNo, ch: ch + len})
      if (typeof mark !== 'undefined') {
        editor.markText({line: lineNo, ch: ch}, {line: lineNo, ch: ch + len}, mark)
      }
      return ch + len
    },
    display_line(proof, lineNo, that) {
      let editor = that.editor
      let line = proof[lineNo]
      let ch = 0
      let strTemp = ''
      for (let i = 0; i < line.id.length; i++) {
        if (line.id[i] === '.') {
          strTemp += '  '
        }
      }
      ch = that.$options.methods.display_str(editor, strTemp, lineNo, ch, {css: 'font-weight: bold'})
      if (line.rule === 'assume') {
        ch = that.$options.methods.display_str(editor, 'assume ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
        ch = that.$options.methods.display_highlight_strs(editor, line.args_hl, lineNo, ch, that)
      } else if (line.rule === 'variable') {
        ch = that.$options.methods.display_str(editor, 'fix ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
        ch = that.$options.methods.display_highlight_strs(editor, line.args_hl, lineNo, ch, that)
      } else if (line.rule === 'subproof') {
        ch = that.$options.methods.display_have_prompt(editor, proof, lineNo, ch, that)
        ch = that.$options.methods.display_highlight_strs(editor, line.th_hl, lineNo, ch, that)
        ch = that.$options.methods.display_str(editor, ' with', lineNo, ch, {css: 'color: darkblue; font-weight: bold'})
      } else {
        // Display theorem with highlight
        if (line.th_hl.length > 0) {
          ch = that.$options.methods.display_have_prompt(editor, proof, lineNo, ch, that)
          ch = that.$options.methods.display_highlight_strs(editor, line.th_hl, lineNo, ch, that)
          ch = that.$options.methods.display_str(editor, ' by ', lineNo, ch, {css: 'font-weight: bold'})
        }
        // Display rule name
        ch = that.$options.methods.display_str(editor, line.rule, lineNo, ch)
        // Display args with highlight
        if (line.args_hl.length > 0) {
          ch = that.$options.methods.display_str(editor, ' ', lineNo, ch)
          ch = that.$options.methods.display_highlight_strs(editor, line.args_hl, lineNo, ch, that)
        }
        if (line.prevs.length > 0) {
          ch = that.$options.methods.display_str(editor, ' from ', lineNo, ch, {css: 'font-weight: bold'})
          ch = that.$options.methods.display_str(editor, line.prevs.join(', '), lineNo, ch)
        }
      }
      editor.execCommand('goDocEnd')
    }
  },
  watch: {
    proof(val) {
      alert(JSON.stringify(val))
      if (this.editor) {
        let that = this
        let editor = this.editor
        let proof = val
        editor.setValue('')
        editor.setOption('lineNumberFormatter', function(lineNo) {
          if (lineNo < proof.length) {
            return proof[lineNo].id
          } else {
            return ''
          }
        })
        let maxIdLen = 0
        proof.forEach(function(line, lineNo) {
          let idLen = line.id.length
          if (idLen >= maxIdLen) {
            maxIdLen = idLen
          }
          that.$options.methods.display_line(proof, lineNo, that)
          let len = editor.getLineHandle(lineNo).text.length
          editor.replaceRange('\n', {line: lineNo, ch: len}, {line: lineNo, ch: len + 1})
          if (line.rule === 'intros') {
            editor.markText({line: lineNo, ch: 0}, {line: lineNo}, {inclusiveRight: true, inclusiveLeft: true, collapsed: 'true'})
          }
        })
      }
    }
  },
  mounted() {
    let that = this
    let editor = CodeMirror.fromTextArea(document.getElementById(this.page_num), {
      mode: 'text/x-python',
      lineNumbers: true,
      firstLineNumber: 0,
      theme: '',
      lineWrapping: false,
      foldGutter: true,
      smartIndent: false,
      matchBrackets: true,
      viewportMargin: Infinity,
      // scrollbarStyle: 'overlay',
      gutters: ['CodeMirror-linenumbers', 'CodeMirror-foldgutter'],
      extraKeys: {
        'Ctrl-I': function () {
          that.apply_method('introduction')
        },
        'Ctrl-B': function () {
          that.apply_method('apply_backward_step')
        },
        'Ctrl-R': function () {
          that.apply_method('rewrite_goal')
        },
        'Ctrl-F': function () {
          that.apply_method('apply_forward_step')
        },
        'Ctrl-Q': function (cm) {
          cm.foldCode(cm.getCursor())
        }
      }
    })
    this.editor = editor
  }
}

</script>

<style scoped>
  .proofArea {
    width: 100%;
    height: 2vh;
  }
</style>
