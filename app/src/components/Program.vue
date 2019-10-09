<template>
  <div>
    <div v-for="(line,index) in lines_edit" :key="index" class="program-line">
      <div v-if="line.ty == 'com'">
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="display-con">{{line.str}}</span>
      </div>
      <div v-else-if="line.ty == 'inv'">
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="line-comment">inv:&nbsp;</span>
        <span class="display-con">{{line.str}}</span>
      </div>
      <div v-else>
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="line-comment">vc:&nbsp;&nbsp;&nbsp;</span>
        <span class="display-con">{{line.str}}</span>
        <span v-if="line.smt" style="margin-left:30px;color:green">OK</span>
        <a href="#" v-else style="margin-left:30px;color:red"
           v-on:click="line.on_proof = true">Failed</a>
        <div v-if="line.on_proof">
          <ProofArea v-bind:theory_name="'hoare'" v-bind:thm_name="undefined"
                    v-bind:vars="line.vars" v-bind:prop="line.prop"
                    v-bind:ref_status="ref_status"
                    v-bind:ref_context="ref_context"
                    ref="proof"
                    v-on:query="handle_query"/>
          <button style="margin:5px" v-on:click="save_proof(index)">Save</button>
          <button style="margin:5px" v-on:click="cancel_proof(index)">Cancel</button>
        </div>
      </div>
    </div> 
  </div>
</template>

<script>
import ProofArea from './ProofArea'

export default {
  name: 'Program',

  props: [
    "lines",

    // Reference to status panel and context panel
    "ref_status",
    "ref_context",
  ],

  data: function () {
    return {
      lines_edit: this.init_lines()
    }
  },

  components: {
    ProofArea
  },

  methods: {
    init_lines: function () {
      const lines_edit = JSON.parse(JSON.stringify(this.lines))
      var has_proof = false
      for (let i = 0; i < lines_edit.length; i++) {
        if (has_proof || lines_edit[i].smt) {
          lines_edit[i].on_proof = false
        } else {
          lines_edit[i].on_proof = true
          has_proof = true
        }
      }
      return lines_edit
    },

    handle_query: function (query) {
      this.$emit('query', query)
    },

    save_proof: function (index) {
      this.lines_edit[index].on_proof = false
    },

    cancel_proof: function (index) {
      this.lines_edit[index].on_proof = false
    }
  },

  watch: {
    lines: function () {
      this.lines_edit = this.init_lines()
    }
  },

  updated() {
    if ('proof' in this.$refs) {
      this.$emit('set-proof', this.$refs.proof[0])
    }
  }
}
</script>

<style scoped>
  .line-comment {
    font-size: 12px;
    margin-right: 2px;
  }

  .program-line {
    margin-left: 20px
  }

  .display-con {
    font-size: 18px;
    font-family: Consolas, monospace;
  }
</style>
