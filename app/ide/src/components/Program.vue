<template>
  <div>
    <div v-for="(line,i) in lines" :key="i" class="program-line">
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
        <span v-if="line.smt" style="margin-left:30px;color:green">
          OK
        </span>
        <span v-else style="margin-left:30px;color:red">
          Failed
        </span>
        <ProofArea v-if="!line.smt" v-bind:theory_name="'hoare'" v-bind:thm_name="undefined"
                   v-bind:vars="line.vars" v-bind:prop="line.prop" ref="proof"/>
      </div>
    </div> 
  </div>
</template>

<script>
import ProofArea from './ProofArea'

export default {
  name: 'Program',

  props: [
    "lines"
  ],

  components: {
    ProofArea
  },

  methods: {
    undo_move: function () {
      this.$refs.proof[0].undo_move()
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
