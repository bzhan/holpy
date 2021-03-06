<template>
  <div align=left v-if="theory !== undefined">
    <div v-if="!edit_metadata">
      <div>
        <span class="keyword">theory</span>&nbsp;<span>{{theory.name}}</span>
        <a href="#" v-on:click="edit_metadata = true" title="edit metadata" style="margin-left:10px">
          <v-icon name="edit"/>
        </a>
      </div>
      <span class="keyword">imports</span>
      <span v-for="(import_name, index) in theory.imports" v-bind:key=index
            v-on:click="$emit('goto-link', import_name)"
            class="import-link">{{import_name}}</span>
      <br><br>
      <span class="comment">{{theory.description}}</span>
      <br><br>
    </div>
    <div v-else>
      <MetadataEdit v-bind:theory="theory" ref="meta_edit"/>
      <button style="margin:5px" v-on:click="save_metadata">Save</button>
      <button style="margin:5px" v-on:click="edit_metadata = false">Cancel</button>
    </div>
    <div v-for="(item, index) in theory.content"
         v-bind:key=index
         v-bind:item_id=index
         class="theory-items"
         v-on:click="handle_select(index, $event)"
         v-on:mousedown="handle_mousedown($event)"
         v-on:mousemove="handle_mousemove($event)"
         ref="items"
         v-bind:class="{
           'item-selected': is_selected(index),
           'item-error': 'error' in item
         }">
      <div v-if="item.ty === 'header'">
        <span class="header-item">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'type.ax'">
        <span class="keyword">type</span>&nbsp;
        <Expression v-bind:line="item.display.type" :editor="editor"/>
      </div>
      <div v-if="item.ty === 'def.ax'">
        <Constant v-if="on_edit !== index" v-bind:item="item.display"
                  v-on:edit="edit_item(index)"
                  :editor="editor"/>
        <div v-else>
          <ConstantEdit v-bind:old_item="item.edit" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'type.ind'">
        <Datatype v-if="on_edit !== index" v-bind:item="item.display"
                  v-on:edit="edit_item(index)"
                  :editor="editor"/>
        <div v-else>
          <DatatypeEdit v-bind:old_item="item.edit" :ext="item.ext" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def'">
        <Definition v-if="on_edit !== index" v-bind:item="item.display"
                    v-on:edit="edit_item(index)"
                    :editor="editor"/>
        <div v-else>
          <DefinitionEdit v-bind:old_item="item.edit" :ext="item.ext" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def.ind'">
        <Inductive v-if="on_edit !== index" v-bind:item="item.display"
                   v-on:edit="edit_item(index)"
                   :editor="editor"/>
        <div v-else>
          <InductiveEdit v-bind:old_item="item.edit" :ext="item.ext" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def.pred'">
        <Inductive v-if="on_edit !== index" v-bind:item="item.display"
                   v-on:edit="edit_item(index)"
                   :editor="editor"/>
        <div v-else>
          <InductiveEdit v-bind:old_item="item.edit" :ext="item.ext" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty == 'thm'">
        <Theorem v-if="on_edit !== index" v-bind:item="item.display" :proof="item.proof" :num_gaps="item.num_gaps"
                 v-on:edit="edit_item(index)" v-on:proof="init_proof(index)"
                 :editor="editor"/>
        <div v-else>
          <TheoremEdit v-bind:old_item="item.edit" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
        <div v-if="on_proof === index">
          <ProofArea v-bind:theory_name="theory.name" v-bind:thm_name="item.name"
                     v-bind:vars="item.vars" v-bind:prop="item.prop"
                     v-bind:old_steps="item.steps" v-bind:old_proof="item.proof"
                     v-bind:ref_status="ref_status" v-bind:ref_context="ref_context"
                     v-bind:editor="editor"
                     ref="proof"
                     v-on:query="handle_query"/>
          <button style="margin:5px" v-on:click="save_proof">Save</button>
          <button style="margin:5px" v-on:click="reset_proof">Reset</button>
          <button style="margin:5px" v-on:click="cancel_proof">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'thm.ax'">
        <Axiom v-if="on_edit !== index" v-bind:item="item.display"
               v-on:edit="edit_item(index)"
               :editor="editor"/>
        <div v-else>
          <TheoremEdit v-bind:old_item="item.edit" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'

import Axiom from './items/Axiom'
import Constant from './items/Constant'
import ConstantEdit from './items/ConstantEdit'
import Datatype from './items/Datatype'
import DatatypeEdit from './items/DatatypeEdit'
import Definition from './items/Definition'
import DefinitionEdit from './items/DefinitionEdit'
import Inductive from './items/Inductive'
import InductiveEdit from './items/InductiveEdit'
import Theorem from './items/Theorem'
import TheoremEdit from './items/TheoremEdit'
import MetadataEdit from './items/MetadataEdit'
import ProofArea from './proof/ProofArea'

export default {
  name: 'Theory',

  components: {
    Axiom,
    Constant,
    ConstantEdit,
    Datatype,
    DatatypeEdit,
    Definition,
    DefinitionEdit,
    Inductive,
    InductiveEdit,
    Theorem,
    TheoremEdit,
    MetadataEdit,
    ProofArea
  },

  props: [
    "theory",

    // Reference to status panel and context panel
    "ref_status",
    "ref_context",

    // Reference to the editor
    "editor"
  ],

  data: function () {
    return {
      // Index of the currently selected item
      selected: {},

      // Index of the currently editing item
      on_edit: undefined,

      // Whether we are currently adding an item
      on_add: false,

      // Index of the current proof
      on_proof: undefined,

      // Whether editing the metadata
      edit_metadata: false,

      // Information for keeping track of mouse movement
      drag: false,
      startingPos: undefined,

      // Keyword translator
      keywords: {
        'def': 'definition',
        'def.ax': 'constant',
        'thm': 'theorem',
        'thm.ax': 'axiom',
        'def.ind': 'fun',
        'def.pred': 'inductive',
        'type.ind': 'datatype'
      },

      // Whether to scroll into position after update
      scroll_after_update: false,
    }
  },

  methods: {
    scrollToSelected: function () {
      if ('single' in this.selected) {
        this.$refs.items[this.selected.single].scrollIntoView({
          block: 'nearest'
        })
      }
      else {
        this.$refs.items[this.selected.end].scrollIntoView({
          block: 'nearest'
        })
      }
    },

    handle_keydown: function (event) {
      if (event.keyCode === 38 && event.ctrlKey) {  // Ctrl+Up
        this.item_move_up()
      } else if (event.keyCode === 40 && event.ctrlKey) { // Ctrl+Down
        this.item_move_down()
      } else if (event.keyCode === 38 && event.shiftKey) {  // Shift+Up
        if ('single' in this.selected && this.selected.single > 0) {
          this.selected = {
            start: this.selected.single,
            end: this.selected.single-1
          }
        } else if ('start' in this.selected && this.selected.end > 0) {
          if (this.selected.end === this.selected.start + 1) {
            this.selected = {single: this.selected.start}
          } else {
            this.selected = {
              start: this.selected.start,
              end: this.selected.end-1
            }
          }
        }
        this.scroll_after_update = true
      } else if (event.keyCode === 40 && event.shiftKey) {  // Shift+Down
        if ('single' in this.selected && this.selected.single < this.theory.content.length-1) {
          this.selected = {
            start: this.selected.single,
            end: this.selected.single+1
          }
        } else if ('start' in this.selected && this.selected.end < this.theory.content.length-1) {
          if (this.selected.end === this.selected.start - 1) {
            this.selected = {single: this.selected.start}
          } else {
            this.selected = {
              start: this.selected.start,
              end: this.selected.end+1
            }
          }
        }
        this.scroll_after_update = true
      }
    },

    handle_mousedown: function (event) {
      this.drag = false
      this.startingPos = [event.pageX, event.pageY];
      if (event.shiftKey) {
        event.preventDefault()
      }
    },

    handle_mousemove: function (event) {
      if ([event.pageX, event.pageY] !== this.startingPos) {
        this.drag = true
      }
    },

    is_selected: function (index) {
      if ('single' in this.selected) {
        return this.selected.single === index
      } else if (this.selected.start <= this.selected.end) {
        return this.selected.start <= index && index <= this.selected.end
      } else {
        return this.selected.end <= index && index <= this.selected.start
      }
    },

    save_metadata: function () {
      this.theory.imports = this.$refs.meta_edit.imports.split('\n')
      this.theory.description = this.$refs.meta_edit.description
      this.save_json_file()
      this.edit_metadata = false
    },

    handle_query: function (query) {
      this.$emit('query', query)
    },

    edit_item: function (index) {
      this.selected = {single: index}
      this.on_edit = index
      this.on_add = false
    },

    // Send an item to the server for parsing.
    parse_item: async function () {
      var limit_ty = undefined
      var limit_name = undefined
      if (this.on_add) {
        if (this.on_edit != this.theory.content.length - 1) {
          limit_ty = this.theory.content[this.on_edit+1].ty
          limit_name = this.theory.content[this.on_edit+1].name
        }
      } else {
        limit_ty = this.theory.content[this.on_edit].ty
        limit_name = this.theory.content[this.on_edit].name
      }
      const data = {
        username: this.$state.user,
        filename: this.theory.name,
        limit_ty: limit_ty,
        limit_name: limit_name,
        line_length: 80,
        item: this.$refs.edit[0]._data.item
      }
      this.$emit('set-message', {
        type: 'OK',
        data: 'Checking...'
      })
      var response = undefined
      try {
        response = await axios.post('http://127.0.0.1:5000/api/check-modify', JSON.stringify(data))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }
      return response
    },

    // Select (or un-select) an item
    handle_select: function (index, event) {
      // Outside selection
      if (event === undefined) {
          this.selected = {single: index}
          this.scroll_after_update = true
          return
      }

      // Ignore if click on a link or button
      if (event.target.tagName.toLowerCase() === 'a' ||
          event.target.tagName.toLowerCase() === 'button') {
        return
      }

      // Ignore if on drag
      if (this.drag) {
        return
      }

      if (event.shiftKey) {
        // Multiple selection
        if (!this.selected) {
          this.selected = {single: index}
        } else if ('single' in this.selected) {
          this.selected = {
            start: this.selected.single,
            end: index
          }
        } else if (this.selected.start === index) {
          this.selected = {single: index}
        } else {
          this.selected = {
            start: this.selected.start,
            end: index
          }
        }
      } else {
        // Single selection
        if ('single' in this.selected && this.selected.single === index) {
          this.selected = {}
        } else {
          this.selected = {single: index}
        }
      }
    },

    // Check whether the current edit produces any errors.
    check_edit: async function () {
      const response = await this.parse_item()
      if (response === undefined)
        return

      const item = response.data.item
      if ('error' in item) {
        this.$emit('set-message', {
          type: 'error',
          data: item.error.err_type + '\n' + item.error.err_str,
          trace: item.error.trace
        })
      } else {
        this.$emit('set-message', {
          type: 'OK',
          data: 'No errors'
        })
      }
    },

    // Save the current edit.
    save_edit: async function () {
      const response = await this.parse_item()
      if (response === undefined)
        return

      const item = this.theory.content[this.on_edit]
      const new_item = response.data.item
      if (item.ty == 'thm') {
        // Copy over proof information
        new_item.proof = item.proof
        new_item.num_gaps = item.num_gaps
        new_item.steps = item.steps
      }
      this.$set(this.theory.content, this.on_edit, new_item)
      this.save_json_file()
      this.on_edit = undefined
      this.on_add = false
    },

    // Cancel the current edit without saving.
    cancel_edit: function () {
      if (this.on_add === true) {
        this.theory.content.splice(this.on_edit, 1)
        this.$set(this.theory, 'content', this.theory.content)
        this.on_add = false
      }
      this.selected = {}
      this.on_edit = undefined
    },

    // Add a new item.
    // ty specifies type of the new item. One of 'thm', 'def', etc.
    // pos specifies where the item should be added. One of 'end', 'before' and 'after'.
    add_item: function (ty, pos) {
      if (this.on_add) {
        // Already adding an item
        return
      }
      if (this.theory === undefined) {
        // Have not loaded any theory
        return
      }
      const new_item = {
        ty: ty, name: '',
        edit: {
          ty: ty, name: ''
        }
      }
      if (pos == 'end') {
        const len = this.theory.content.length
        this.$set(this.theory.content, len, new_item)
        this.selected = {single: len}
      } else if (pos == 'before') {
        if (!('single' in this.selected)) {
          return
        }
        this.theory.content.splice(this.selected.single, 0, {})
        this.$set(this.theory.content, this.selected.single, new_item)
      } else if (pos == 'after') {
        if (!('single' in this.selected)) {
          return
        }
        this.theory.content.splice(this.selected.single+1, 0, {})
        this.$set(this.theory.content, this.selected.single+1, new_item)
        this.selected = {single: this.selected.single+1}
      }
      this.on_edit = this.selected.single
      this.on_add = true
      this.scroll_after_update = true
    },

    remove_selected: function () {
      if ('single' in this.selected) {
        this.theory.content.splice(this.selected.single, 1)
        this.$set(this.theory, 'content', this.theory.content)
        this.save_json_file()
      }
    },

    item_move_up: function () {
      var start = this.select_start
      var end = this.select_end
      if (start !== undefined && start > 0) {
        var swap = this.theory.content[start-1]
        for (let i = start; i <= end; i++) {
          this.$set(this.theory.content, i-1, this.theory.content[i])
        }
        this.$set(this.theory.content, end, swap)
        this.save_json_file()
        if ('single' in this.selected) {
          this.selected = {single: this.selected.single-1}
        } else {
          this.selected = {
            start: this.selected.start-1,
            end: this.selected.end-1
          }
        }
      }
    },

    item_move_down: function () {
      var start = this.select_start
      var end = this.select_end
      if (end !== undefined && end < this.theory.content.length-1) {
        var swap = this.theory.content[end+1]
        for (let i = end; i >= start; i--) {
          this.$set(this.theory.content, i+1, this.theory.content[i])
        }
        this.$set(this.theory.content, start, swap)
        this.save_json_file()
        if ('single' in this.selected) {
          this.selected = {single: this.selected.single+1}
        } else {
          this.selected = {
            start: this.selected.start+1,
            end: this.selected.end+1
          }
        }
      }
    },

    // Save all changed proof on the webpage to the json-file;
    save_json_file: async function () {
      var content = [];
      for (let i = 0; i < this.theory.content.length; i++) {
        const item = this.theory.content[i]
        if ('name' in item) {
          var item_copy = JSON.parse(JSON.stringify(item)) // deep copy
          delete item_copy.error
          delete item_copy.display
          delete item_copy.edit
          delete item_copy.ext
          content.push(item_copy);
        }
      }

      const data = {
        username: this.$state.user,
        filename: this.theory.name,
        content: {
          name: this.theory.name,
          imports: this.theory.imports,
          description: this.theory.description,
          content: content
        }
      }

      var response = undefined
      try {
        response = await axios.post('http://127.0.0.1:5000/api/save-file', JSON.stringify(data))
      } catch (err) {
        this.$emit('set-message', {
          type: 'error',
          data: 'Server error'
        })
      }

      if (response !== undefined) {
        this.$emit('set-message', {
          type: 'OK',
          data: 'Saved'
        })
      }
    },

    init_proof: function (index) {
      this.on_proof = index
      this.selected = {single: index}
      this.scroll_after_update = true
    },

    save_proof: function () {
      const $proof = this.$refs.proof[0]
      var item = this.theory.content[this.on_proof]

      if ($proof.steps.length === 0) {
        // Force update
        this.$delete(this.theory.content[this.on_proof], 'proof')
        delete item.num_gaps
        delete item.steps
      } else {
        const cur_proof = $proof.proof
        item.num_gaps = $proof.num_gaps
        var output_proof = []
        for (let i = 0; i < cur_proof.length; i++) {
          output_proof.push(JSON.parse(JSON.stringify(cur_proof[i])))  // deep copy
          delete output_proof[i].th_hl
          delete output_proof[i].args_hl
        }

        // Force update
        this.$set(this.theory.content[this.on_proof], 'proof', output_proof)
        item.steps = $proof.steps
      }

      this.save_json_file()
      this.on_proof = undefined
    },

    reset_proof: function () {
      this.$refs.proof[0].init_empty_proof()
    },

    cancel_proof: function () {
      this.on_proof = undefined
    },

    selected_set_message: function () {
      if ('single' in this.selected) {
        const item = this.theory.content[this.selected.single]
        if ('error' in item) {
          // Selected item, which has an error
          this.$emit('set-message', {
            type: 'error',
            data: item.error.err_type + '\n' + item.error.err_str
          })
        } else {
          // Selected item, with no errors
          this.$emit('set-message', {
            type: 'OK',
            data: 'No errors'
          })
        }
      } else if ('start' in this.selected) {
        var num_item = this.select_end - this.select_start + 1
        this.$emit('set-message', {
          type: 'OK',
          data: num_item + ' items selected'
        })
      } else {
        // No item selected, determine whether there are errors
        // in the file
        var err_count = 0
        var err_lines = ''
        for (let i = 0; i < this.theory.content.length; i++) {
          let item = this.theory.content[i]
          if ('error' in item) {
            err_count += 1
            err_lines += ('\n' + this.keywords[item.ty] + ' ' + item.name)
          }
        }
        if (err_count !== 0) {
          this.$emit('set-message', {
            type: 'error',
            data: 'Loaded ' + this.theory.name + ': ' + err_count + ' error(s)' + err_lines
          })
        } else {
          this.$emit('set-message', {
            type: 'OK',
            data: 'Loaded ' + this.theory.name + ': ' + 'OK '
          })
        }
      }
    }
  },

  computed: {
    select_start: function () {
      if ('single' in this.selected) {
        return this.selected.single
      } else if ('start' in this.selected) {
        return Math.min(this.selected.start, this.selected.end)
      } else {
        return undefined
      }
    },

    select_end: function () {
      if ('single' in this.selected) {
        return this.selected.single
      } else if ('start' in this.selected) {
        return Math.max(this.selected.start, this.selected.end)
      } else {
        return undefined
      }
    }
  },

  watch: {
    selected: function () {
      this.selected_set_message()
    },

    theory: function () {
      this.selected = {}
      this.selected_set_message()
    }
  },

  updated() {
    if ('proof' in this.$refs) {
      this.$emit('set-proof', this.$refs.proof[0])
    }
    if (this.scroll_after_update) {
      this.scroll_after_update = false
      this.scrollToSelected()
    }
  },

  created() {
    window.addEventListener('keydown', (event) => {
      this.handle_keydown(event)
    })
  }
}
</script>

<style scoped>

.import-link {
  margin-left: 5px;
}

.import-link:hover {
  text-decoration: underline;
  cursor: pointer;
}

.theory-items {
  margin: 3px;
  padding: 5px;
}

.comment {
  color: green;
}

.header-item {
  font-size: 14pt;
}

.item-error {
  background-color: rgb(255, 212, 212);
}

.item-selected {
  border-style: solid;
  border-width: thin;
}

</style>
