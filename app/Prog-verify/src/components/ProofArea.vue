<template>
  <div class="tab-pane fade active code-cell">
    <label :for=page_num></label>
    <textarea :id=page_num v-model="proof" class="proofArea"></textarea>
    <br>
    <info ref="info"/>
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
      textId: 0
    }
  },
  methods: {
    get_selected_id: function() {
      return this.textId
    },
    match_thm: function(proof) {
      var id = this.get_selected_id()
      var input = this.current_state()
      if (input === undefined) {
        cells[id].search_res = []
        this.display_match_thm()
      } else {
        axios({
          url: '/api/search-method',
          type: 'POST',
          data: JSON.stringify(input),
          success: function (result) {
            cells[id].search_res = result.search_res
            this.display_match_thm()
          }
        })
      }
    },
    apply_method: function(methodName, args) {
      var count = 0
      var sigList = []
      var id = this.get_selected_id()
      var sigs = cells[id].method_sig[methodName]
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
      axios({
        method: 'post',
        url: 'http://127.0.0.1:5000/api/apply-method',
        data: JSON.stringify(input),
        success: function(result) {
          if ('query' in result) {
            // Query for more parameters
            var templ_query = _.template($('#template-query').html())
            var sig_list = result.query.map(s => s === 'names' ? s : s.slice(6)) // get rid of 'param_'
            var input_html = templ_query({sig_list: sig_list})
            this.$swal({
              title: 'Query for parameters',
              html: input_html,
              showCancelButton: true,
              stopKeydownPropagation: false,
              focusConfirm: false,
              confirmButtonText: 'Confirm',
              cancelButtonText: 'Cancel',
              preConfirm: () => {
                for (let i = 0; i < sig_list.length; i++) {
                  var sig = sig_list[i] === 'names' ? sig_list[i] : 'param_' + sig_list[i]
                  input[sig] = document.getElementById('sig-input' + (i + 1)).value
                }
              }
            }).then(function (isConfirm) {
              if (isConfirm.value) {
                this.options.methods.apply_method_ajax(input)
              }
            })
          } else if ('failed' in result) {
            display_status(result.failed + ': ' + result.message, 'red')
          } else {
            // Success
            var id = input.id
            var h_id = cells[id].index
            cells[id].steps[h_id] = input
            cells[id].steps.length = h_id + 1
            cells[id].history[h_id].steps_output = result.steps_output
            cells[id].history[h_id + 1] = {
              'steps_output': [['Current state', 0]],
              'proof': result.proof,
              'report': result.report
            }
            cells[id].history.length = h_id + 2
            delete input.id
            if (input.fact_ids.length == 0) { delete input.fact_ids }
            delete input.theory_name
            delete input.thm_name
            delete input.vars
            delete input.proof
            cells[id].index += 1
            display_instructions()
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
      if (that.$options.methods.is_last_id(proof, lineNo)) {
        return that.$options.methods.display_str(editor, 'show ', lineNo, ch, {css: 'color: darkcyan; font-weight: bold'})
      } else {
        return that.$options.methods.display_str(editor, 'have ', lineNo, ch, {css: 'color: darkblue; font-weight: bold'})
      }
    },
    display_highlight_str(editor, p, lineNo, ch, that) {
      let color
      if (p[1] === 0) { color = 'color: black' } else if (p[1] === 1) { color = 'color: green' } else if (p[1] === 2) { color = 'color: blue' } else if (p[1] === 3) { color = 'color: purple' } else if (p[1] === 4) { color = 'color: silver' }
      return that.$options.methods.display_str(editor, p[0], lineNo, ch, {css: color})
    },
    display_highlight_strs(editor, ps, lineNo, ch, that) {
      for (let i = 0; i < ps.length; i++) {
        ch = that.$options.methods.display_highlight_str(editor, ps[i], lineNo, ch, that)
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
