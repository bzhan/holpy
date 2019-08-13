<template>
  <div class="tab-pane fade active code-cell">
    <label :for=page_num></label>
    <textarea :id=page_num v-model="proof" class="proofArea"></textarea>
    <br>
    <label></label>
  </div>
</template>

<script>
import 'codemirror/lib/codemirror.css'
let CodeMirror = require('codemirror/lib/codemirror')

export default {
  name: 'proofArea',
  props: ['page_num', 'proof'],
  data: function () {
    return {
      text: 'asdas',
      editor: ''
    }
  },
  methods: {
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
    display_highlight_strs(editor, ps, line_no, ch, that) {
      for (let i = 0; i < ps.length; i++) {
          ch = that.$options.methods.display_highlight_str(editor, ps[i], line_no, ch, that);
      }
      return ch;
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
      gutters: ['CodeMirror-linenumbers', 'CodeMirror-foldgutter']
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
