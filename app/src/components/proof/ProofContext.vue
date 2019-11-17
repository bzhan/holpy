<template>
  <div style="margin-left:10px;margin-top:10px">
    <div style="font-size:18px;margin-bottom:5px">Variables</div>
    <div style="height:70px;overflow-y:scroll">
      <div style="margin-left:10px" v-for="(T, nm, index) in ctxt" v-bind:key="index">
        <span class="item-text">{{nm}}</span> :: <Expression v-bind:line="T"/>
      </div>
    </div>
    <div style="margin-top:10px;margin-bottom:5px;font-size:18px">History</div>
    <div>
      <div v-for="(line, index) in steps" v-bind:key="index"
           style="white-space:nowrap"
           v-on:mouseenter="handleMouseEnter(index)"
           v-on:mouseleave="handleMouseLeave(index)">
        <v-icon style="color:red" title="delete" name="times"
            v-on:click.native="handleDelete(index)"
            v-show="line.hover === true"/>
        <Expression style="margin-left:5px" v-bind:line="line.steps_output" 
            v-on:click.native="handleSelect(index)"
            v-bind:class="{
              'step-entry': true,
              'step-selected': selected_step === index,
              'step-unread': !line.is_read,
              'step-error': line.is_read && line.error !== undefined}"/>
      </div>
    </div>
  </div>
</template>

<script>

export default {
  name: 'ProofContext',

  props: [
    // Proof area linked to this context.
    'ref_proof'
  ],

  data: function () {
    return {
      // Context: mapping from variables to their types.
      ctxt: undefined,

      // History information.
      steps: undefined,
      selected_step: undefined
    }
  },

  methods: {
    handleMouseEnter: function (index) {
      this.$set(this.steps[index], 'hover', true)
    },

    handleMouseLeave: function (index) {
      this.$set(this.steps[index], 'hover', false)
    },

    handleSelect: function (index) {
      this.ref_proof.gotoStep(index)
    },

    handleDelete: function (index) {
      this.ref_proof.deleteStep(index)
    }
  }
}
</script>


<style>

.step-entry {
  cursor: pointer
}

.step-selected {
  border: 1px solid black
}

.step-error {
  background-color: red
}

.step-unread {
  background-color: pink
}

</style>
