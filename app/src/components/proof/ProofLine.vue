<template>
  <div v-if="line !== undefined && line.rule !== 'intros'" style="font-size:14px;white-space:nowrap"
       v-bind:style="styleObject" v-on:click="$emit('select')">
    <span style="display:inline-block;width:40px">{{line.id}}</span>
    <span class="item-text" v-html="indent"/>
    <span v-if="line.rule === 'assume'">
      <span class="item-text keyword2">assume </span>
      <Expression v-bind:line="line.args_hl"/>
    </span>
    <span v-else-if="line.rule === 'variable'">
      <span class="item-text keyword2">fix </span>
      <Expression v-bind:line="line.args_hl"/>
    </span>
    <span v-else-if="line.rule === 'subproof'">
      <span class="item-text keyword1">have </span>
      <Expression v-bind:line="line.th_hl"/>
      <span class="item-text keyword1"> with</span>
    </span>
    <span v-else>
      <span v-if="is_last_id" class="item-text keyword2">show </span>
      <span v-else class="item-text keyword1">have </span>
      <Expression v-bind:line="line.th_hl"/>
      <span class="item-text keyword3"> by </span>
      <span v-if="line.rule === 'sorry' && is_goal" class="item-text" style="background-color:red">sorry</span>
      <span v-else class="item-text">{{line.rule}}</span>
      <span v-if="line.args_hl.length > 0">
        <span class="item-text">&nbsp;</span>
        <Expression v-bind:line="line.args_hl"/>
      </span>
      <span v-if="line.prevs.length > 0">
        <span class="item-text keyword3"> from </span>
        <span class="item-text">{{line.prevs.join(', ')}}</span>
      </span>
    </span>
  </div>
</template>

<script>
export default {
  name: 'ProofLine',

  props: [
    // Line of proof to be displayed
    "line",

    // Used to decide between have/show.
    "is_last_id",

    // Whether is a goal or fact.
    "is_goal",
    "is_fact",
  ],

  computed: {
    indent: function () {
      var indent = ''
      for (let i = 0; i < this.line.id.length; i++) {
        if (this.line.id[i] === '.') {
          indent += '&nbsp;&nbsp;'
        }
      }
      return indent
    },

    styleObject: function () {
      if (this.is_fact) {
        return {backgroundColor: 'yellow'}
      } else {
        return {}
      }
    }
  }
}
</script>

<style scoped>

.keyword1 {
  color: darkblue;
  font-weight: bold;
}

.keyword2 {
  color: darkcyan;
  font-weight: bold;
}

.keyword3 {
  color: black;
  font-weight: bold;
}

</style>
