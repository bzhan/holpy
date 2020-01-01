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
      <Expression style="margin-left:5px"
          v-bind:line="[{color: 0, text: 'Initial'}]"
          v-on:click.exact.native="handleSelect(0)"
          v-on:click.shift.native="handleShiftSelect(0)"
          v-bind:class="{
            'step-entry': true,
            'step-selected': isSelected(0)}"/>
      <div v-for="(line, index) in steps" v-bind:key="index"
           style="white-space:nowrap">
        <Expression style="margin-left:5px" v-bind:line="line.step_output" 
            v-on:click.exact.native="handleSelect(index+1)"
            v-on:click.shift.native="handleShiftSelect(index+1)"
            v-bind:class="{
              'step-entry': true,
              'step-selected': isSelected(index+1),
              'step-error': line.error !== undefined}"/>
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
      selected_start: undefined,
      selected_end: undefined
    }
  },

  methods: {
    isSelected: function (index) {
      if (this.selected_start <= this.selected_end) {
        return this.selected_start <= index && index <= this.selected_end
      } else {
        return this.selected_end <= index && index <= this.selected_start
      }
    },

    handleSelect: function (index) {
      this.setSelectedSingle(index)
      this.ref_proof.gotoStep(index)
    },

    handleShiftSelect: function (index) {
      this.selected_end = index
      this.ref_proof.gotoStep(index)
    },

    deleteStep: function () {
      var start = Math.max(0, this.selected_start - 1)
      var end = Math.max(0, this.selected_end - 1)
      if (start > end) {
        [start, end] = [end, start]
      }
      this.setSelectedSingle(start)
      this.ref_proof.deleteStep(start, end)
    },

    setSelectedSingle: function (index) {
      this.selected_start = index
      this.selected_end = index
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

</style>
