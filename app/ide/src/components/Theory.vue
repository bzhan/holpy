<template>
  <div align=left v-if="theory !== undefined">
    <span class="keyword">theory</span>&nbsp;{{theory.name}}
    <br>
    <span class="keyword">imports</span>&nbsp;{{theory.imports.join(' ')}}
    <br><br>
    <span class="comment">{{theory.description}}</span>
    <br><br>
    <div v-for="(item, index) in theory.content"
         v-bind:key=index
         v-bind:item_id=index
         class="theory-items"
         v-on:click="handle_select(index, $event)"
         v-bind:class="{
           'item-selected': selected === index,
           'item-error': 'err_type' in item
         }">
      <div v-if="item.ty === 'header'">
        <span class="header-item">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'type.ax'">
        <span class="keyword">type</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'def.ax'">
        <Constant v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <ConstantEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'type.ind'">
        <Datatype v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <DatatypeEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def'">
        <Definition v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <DefinitionEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def.ind'">
        <Inductive v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <DefinitionEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'def.pred'">
        <Inductive v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <DefinitionEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'macro'">
        <span class="keyword">macro</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'method'">
        <span class="keyword">method</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty == 'thm'">
        <Theorem v-if="on_edit !== index" v-bind:item="item"
                 v-on:edit="edit_item(index)" v-on:proof="init_proof(index)"/>
        <div v-else>
          <TheoremEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
        <div v-if="on_proof === index">
          <ProofArea v-bind:theory_name="theory.name" v-bind:thm_name="item.name"
                     v-bind:vars="item.vars" v-bind:prop="item.prop"
                     v-bind:old_steps="item.steps" v-bind:old_proof="item.proof"
                     v-bind:ref_status="ref_status" v-bind:ref_context="ref_context"
                     ref="proof"
                     v-on:query="handle_query"/>
          <button style="margin:5px" v-on:click="save_proof">Save</button>
          <button style="margin:5px" v-on:click="reset_proof">Reset</button>
          <button style="margin:5px" v-on:click="cancel_proof">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'thm.ax'">
        <Axiom v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <TheoremEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import Util from './../../static/js/util.js'
import axios from 'axios'

import Axiom from './items/Axiom'
import Constant from './items/Constant'
import ConstantEdit from './items/ConstantEdit'
import Datatype from './items/Datatype'
import DatatypeEdit from './items/DatatypeEdit'
import Definition from './items/Definition'
import DefinitionEdit from './items/DefinitionEdit'
import Inductive from './items/Inductive'
import Theorem from './items/Theorem'
import TheoremEdit from './items/TheoremEdit'
import ProofArea from './ProofArea'

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
    Theorem,
    TheoremEdit,
    ProofArea,
  },

  props: [
    "theory",

    // Reference to status panel and context panel
    "ref_status",
    "ref_context"
  ],

  data: function () {
    return {
      // Index of the currently selected item
      selected: undefined,

      // Index of the currently editing item
      on_edit: undefined,

      // Whether we are currently adding an item
      on_add: false,

      // Index of the current proof
      on_proof: undefined,
    }
  },

  methods: {
    handle_query: function (query) {
      this.$emit('query', query)
    },

    edit_item: function (index) {
      this.selected = index
      this.on_edit = index
      this.on_add = false
    },

    // Send an item to the server for parsing.
    parse_item: async function () {
      const data = {
        file_name: this.theory.name,
        prev_list: this.theory.content.slice(0, Number(this.on_edit)),
        line_length: 80,
        content: this.$refs.edit[0]._data.item
      }
      delete data.content.err_type
      delete data.content.err_str
      delete data.content.trace
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
      // Ignore if click on a link
      if (event.target.tagName.toLowerCase() === 'a') {
        return
      }

      // Ignore if currently editing or proving something
      if (this.on_edit !== undefined || this.on_proof !== undefined) {
        return
      }

      if (this.selected === index) {
        this.selected = undefined
      } else {
        this.selected = index
      }
    },

    // Check whether the current edit produces any errors.
    check_edit: async function () {
      const response = await this.parse_item()
      if (response === undefined)
        return

      const item = response.data.item
      if ('err_type' in item) {
        this.$emit('set-message', {
          type: 'error',
          data: item.err_type + '\n' + item.err_str,
          trace: item.trace
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

      var item = this.theory.content[this.on_edit]
      delete item.err_type
      delete item.err_str
      delete item.trace
      Object.assign(item, response.data.item)
      this.$set(this.theory.content, this.on_edit, item)
      this.save_json_file()
      this.on_edit = undefined
      this.on_add = false
    },

    // Cancel the current edit without saving.
    cancel_edit: function () {
      this.on_edit = undefined
      if (this.on_add === true) {
        this.remove_selected()
        this.on_add = false
      }
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
      if (pos == 'end') {
        const len = this.theory.content.length
        this.$set(this.theory.content, len, {ty: ty})
        this.selected = len
      } else if (pos == 'before') {
        if (this.selected === undefined) {
          return
        }
        this.theory.content.splice(this.selected, 0, {})
        this.$set(this.theory.content, this.selected, {ty: ty})
      } else if (pos == 'after') {
        if (this.selected === undefined) {
          return
        }
        this.theory.content.splice(this.selected+1, 0, {})
        this.$set(this.theory.content, this.selected+1, {ty: ty})
        this.selected += 1
      }
      this.on_edit = this.selected
      this.on_add = true
    },

    remove_selected: function () {
      if (this.selected === undefined)
        return

      this.theory.content.splice(this.selected, 1)
      this.$set(this.theory, 'content', this.theory.content)
      this.save_json_file()
    },

    // Convert items in the theory from json format for the web client
    // back to the json format for the file.
    item_to_output: function (data) {
      if (data.ty === 'def.ax') {
        delete data.type_hl;
      } else if (data.ty === 'thm' || data.ty === 'thm.ax') {
        delete data.prop_hl;
        delete data.prop_lines;
        delete data.vars_lines;
      } else if (data.ty === 'type.ind') {
        delete data.constrs_hl;
        delete data.constrs_lines;
        delete data.type_hl;
        delete data.edit_type;
        delete data.ext;
      } else if (data.ty === 'def') {
        delete data.type_hl;
        delete data.prop_hl;
        delete data.prop_lines;
        delete data.ext;
      } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
        delete data.type_hl;
        delete data.ext;
        delete data.prop_lines;
        delete data.ext;
        for (var i in data.rules) {
          delete data.rules[i].prop_hl;
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
          content.push(item_copy);
          this.item_to_output(item_copy);
        }
      }

      const data = {
        name: this.theory.name,
        imports: this.theory.imports,
        description: this.theory.description,
        content: content
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
        var cur_proof = undefined
        if ($proof.history !== undefined) {
          const len = $proof.history.length
          cur_proof = $proof.history[len-1].proof
          item.num_gaps = $proof.history[len-1].report.num_gaps
        } else {
          cur_proof = $proof.proof
          item.num_gaps = $proof.num_gaps
        }

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

    selected_set_message: function (index) {
      if (index !== undefined) {
        const item = this.theory.content[index]
        if ('err_type' in item) {
          // Selected item, which has an error
          this.$emit('set-message', {
            type: 'error',
            data: item.err_type + '\n' + item.err_str
          })
        } else {
          // Selected item, with no errors
          this.$emit('set-message', {
            type: 'OK',
            data: 'No errors'
          })
        }
      } else {
        // No item selected, determine whether there are errors
        // in the file
        var err_count = 0
        var err_lines = ''
        for (let i = 0; i < this.theory.content.length; i++) {
          let item = this.theory.content[i]
          if ('err_type' in item) {
            err_count += 1
            err_lines += ('\n' + Util.keywords[item.ty] + ' ' + item.name)
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

  watch: {
    selected: function (index) {
      this.selected_set_message(index)
    },

    theory: function () {
      this.selected = undefined
      this.selected_set_message(undefined)
    }
  },

  updated() {
    if ('proof' in this.$refs) {
      this.$emit('set-proof', this.$refs.proof[0])
    }
  },

  created() {
    this.Util = Util
  }
}
</script>

<style>

.theory-items {
    margin: 3px;
    padding: 5px;
}

.keyword {
    font-weight: bold;
    color: #006000;
}

.comment {
    color: green;
}

.header-item {
    font-size: 14pt;
}

.indented-text {
    margin-left: 0.8em;
}

.item-error {
  background-color: rgb(255, 212, 212);
}

.item-selected {
  border-style: solid;
  border-width: thin;
}

</style>
