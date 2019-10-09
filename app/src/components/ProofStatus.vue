<template>
  <div>
    <div><span class="item-text">{{ status }}</span></div>
    <div>
      <span v-if="instr_no !== ''">
        <a href="#" id="link-backward" v-on:click="ref_proof.step_backward()">&lt;</a>
        <span id="instruction-number" v-html="instr_no"/>
        <a href="#" id="link-forward" v-on:click="ref_proof.step_forward()">&gt;</a>
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
