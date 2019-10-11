<template>
  <div>
    <div>
      <span class="item-text">{{ status }}</span>
      <a href="#" v-if="trace !== undefined" v-on:click="show_trace = !show_trace">
        {{ show_trace ? 'Hide stack trace' : 'Show stack trace' }}
      </a>
      <pre v-if="trace !== undefined && show_trace">{{trace}}</pre>
    </div>
    <div>
      <span v-if="instr_no !== ''">
        <a href="#" v-on:click="ref_proof.step_backward()">&lt;</a>
        <span id="instruction-number" v-html="instr_no"/>
        <a href="#" v-on:click="ref_proof.step_forward()">&gt;</a>
      </span>
      <Expression style="margin-left:10pt" v-bind:line="instr"/>
    </div>
    <div class="thm-content">
      <div v-for="(res,i) in search_res"
           :key="res.num"
           v-on:click="ref_proof.apply_thm_tactic(i)">
        <Expression v-bind:line="res.display"/>
      </div>
    </div>
  </div>
</template>

<script>

export default {
  name: 'ProofStatus',

  props: [
    // Proof area linked to this status panel
    'ref_proof',
  ],

  data: function () {
    return {
      // Display of current instruction (as a highlighted line)
      instr: [],

      // Display of instruction number
      instr_no: '',
      
      // Display of status (text)
      status: '',

      // Trace of exception
      trace: undefined,

      // Whether to show trace
      show_trace: false,

      // List of search results
      search_res: [],
    }
  },
}
</script>

<style scoped>
.thm-content {
  margin-top: 10px;
  margin-left: 5px;
}

.thm-content div {
  margin: 5px;
}

.thm-content div:hover {
  background-color: yellow;
}

</style>
