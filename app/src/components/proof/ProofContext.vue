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
      <div style="margin-left:10px" v-for="(line, index) in steps" v-bind:key="index"
           v-on:click="handleSelect(index)"
           class='step-entry'
           v-bind:class="{
             'step-selected': selected_step === index,
             'step-error': line.error !== undefined}">
        <Expression v-bind:line="line.steps_output"/>
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
    handleSelect: function (index) {
      this.ref_proof.goto_index(index)
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
