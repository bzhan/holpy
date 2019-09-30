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
         v-on:click="selected = index"
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
        <span class="keyword">constant</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>
      </div>
      <div v-if="item.ty === 'type.ind'">
        <span class="keyword">datatype</span>&nbsp;
        <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span> =
        <span v-for="(v, i) in item.constr_output_hl" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="Util.highlight_html(v)"></span>
        </span>
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
        <span class="keyword">fun</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <span v-for="(v, i) in item.rules" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="Util.highlight_html(v.prop_hl)"></span>
        </span>
      </div>
      <div v-if="item.ty === 'def.pred'">
        <span class="keyword">inductive</span>&nbsp;
        <span class="item-text">{{item.name}}</span> :: 
        <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <span v-for="(v, i) in item.rules" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="Util.highlight_html(v.prop_hl)"></span>
        </span>
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
        <Theorem v-if="on_edit !== index" v-bind:item="item" v-on:edit="edit_item(index)"/>
        <div v-else>
          <TheoremEdit v-bind:old_item="item" ref="edit"/>
          <button style="margin:5px" v-on:click="check_edit">Check</button>
          <button style="margin:5px" v-on:click="save_edit">Save</button>
          <button style="margin:5px" v-on:click="cancel_edit">Cancel</button>
        </div>
      </div>
      <div v-if="item.ty === 'thm.ax'">
        <span class="keyword">axiom</span>&nbsp;
        <span class="item-text">{{item.name}}</span>:
        <br>
        <span v-if="'prop_hl' in item">
          <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
            <span class="item-text indented-text" v-html="Util.highlight_html(line)"></span><br>
          </span>
        </span>
      </div>
    </div>
  </div>
</template>

<script>
import Util from './../../static/js/util.js'
import axios from 'axios'

import Definition from './items/Definition'
import DefinitionEdit from './items/DefinitionEdit'
import Theorem from './items/Theorem'
import TheoremEdit from './items/TheoremEdit'

export default {
  name: 'Theory',

  components: {
    Theorem,
    TheoremEdit,
    Definition,
    DefinitionEdit,
  },

  props: [
    "theory"
  ],

  data: function () {
    return {
      selected: undefined,
      on_edit: undefined
    }
  },

  methods: {
    edit_item: function (index) {
      this.on_edit = index
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

    check_edit: async function () {
      const response = await this.parse_item()
      if (response === undefined)
        return

      if ('err_type' in response.data.item) {
        this.$emit('set-message', {
          type: 'error',
          data: response.data.item.err_str,
          trace: response.data.item.trace
        })
      } else {
        this.$emit('set-message', {
          type: 'OK',
          data: 'No errors'
        })
      }
    },

    save_edit: async function () {
      const response = await this.parse_item()
      if (response === undefined)
        return

      var item = this.theory.content[this.on_edit]
      delete item.err_type
      delete item.err_str
      delete item.trace
      $.extend(item, response.data.item)
      this.$set(this.theory.content, this.on_edit, item)
      this.save_json_file()
      this.on_edit = undefined
    },

    cancel_edit: function () {
      this.on_edit = undefined
    },

    add_theorem: function () {
      const len = this.theory.content.length
      this.$set(this.theory.content, len, {'ty': 'thm'})
      this.selected = len
      this.on_edit = len
    },

    add_definition: function () {
      const len = this.theory.content.length
      this.$set(this.theory.content, len, {'ty': 'def'})
      this.selected = len
      this.on_edit = len
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
        delete data.err_type;
        delete data.err_str;
        delete data.trace;
      } else if (data.ty === 'type.ind') {
        delete data.constr_output;
        delete data.constr_output_hl;
        delete data.type_hl;
        delete data.edit_type;
        delete data.ext_output;
      } else if (data.ty === 'def') {
        delete data.type_hl;
        delete data.prop_hl;
        delete data.prop_lines;
      } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
        delete data.type_hl;
        delete data.ext;
        delete data.edit_content;
        delete data.ext_output;
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
          var item_copy = {};
          $.extend(true, item_copy, item);
          content.push(item_copy);  // perform deep copy
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
    }
  },

  watch: {
    selected: function (index) {
      if (index !== undefined) {
        const item = this.theory.content[index]
        if ('err_type' in item) {
          this.$emit('set-message', {
            type: 'error',
            data: item.err_str
          })
        } else {
          this.$emit('set-message', {
            type: 'OK',
            data: 'No errors'
          })
        }
      } else {
        this.$emit('set-message', {
          type: 'OK',
          data: ""
        })
      }
    }
  },

  created() {
    this.Util = Util
  },
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
