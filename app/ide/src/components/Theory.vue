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
        <span class="keyword">definition</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="Util.highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <br>
        <span class="item-text indented-text" v-html="Util.highlight_html(item.prop_hl)"></span>
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
          <TheoremEdit v-bind:old_item="item"/>
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
import Theorem from './items/Theorem'
import TheoremEdit from './items/TheoremEdit'



export default {
  name: 'Theory',

  components: {
    Theorem,
    TheoremEdit,
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

    save_edit: function () {
      this.on_edit = undefined
    },

    cancel_edit: function () {
      this.on_edit = undefined
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

.theory-items + div {
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
