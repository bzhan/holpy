<template>
  <div>
    <div v-for="(line,index) in lines" :key="index" class="program-line">
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
           v-on:click="on_proof = index">Failed</a>
        <div v-if="on_proof === index">
          <ProofArea v-bind:theory_name="'hoare'" v-bind:thm_name="''"
                    v-bind:vars="line.vars" v-bind:prop="line.prop"
                    v-bind:ref_status="ref_status"
                    v-bind:ref_context="ref_context"
                    ref="proof"
                    v-on:query="handle_query"/>
          <button style="margin:5px" v-on:click="save_proof()">Save</button>
          <button style="margin:5px" v-on:click="reset_proof()">Reset</button>
          <button style="margin:5px" v-on:click="cancel_proof()">Cancel</button>
        </div>
      </div>
    </div> 
  </div>
</template>

<script>
import ProofArea from './proof/ProofArea'

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
      on_proof: undefined
    }
  },

  components: {
    ProofArea
  },

  methods: {
    init_lines: function () {
      for (let i = 0; i < this.lines.length; i++) {
        if (!this.lines[i].smt) {
          this.on_proof = i
          break
        }
      }
    },

    handle_query: function (query) {
      this.$emit('query', query)
    },

    save_proof: function () {
      const $proof = this.$refs.proof[0]
      var cur_proof, output_proof

      if ($proof.steps.length !== 0) {
        const len = $proof.history.length
        cur_proof = $proof.history[len-1].proof

        output_proof = []
        for (let i = 0; i < cur_proof.length; i++) {
          output_proof.push(JSON.parse(JSON.stringify(cur_proof[i])))  // deep copy
          delete output_proof[i].th_hl
          delete output_proof[i].args_hl
        }
      }

      this.$emit('save-proof', output_proof)
      this.on_proof = undefined
    },

    reset_proof: function () {
      this.$refs.proof[0].init_empty_proof()
    },

    cancel_proof: function () {
      this.on_proof = undefined
    }
  },

  watch: {
    lines: function () {
      this.init_lines()
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
