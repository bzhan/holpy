<template>
  <div>
    <div><pre>{{ status }}</pre></div>
    <div>
      <a href="#" id="link-backward" v-on:click="ref_proof.step_backward()">&lt;</a>
      <span id="instruction-number" v-html="instr_no"/>
      <a href="#" id="link-forward" v-on:click="ref_proof.step_forward()">&gt;</a>
      <span id="instruction" style="margin-left:10pt" v-html="instr"/>
    </div>
    <div class="thm-content">
      <pre v-for="(res,i) in search_res"
           :key="res.num"
           v-on:click="ref_proof.apply_thm_tactic(i)"
           v-html="Util.highlight_html(res.display)"/>
    </div>
  </div>
</template>

<script>
import Util from './../../static/js/util.js'

export default {
  name: 'ProofStatus',

  props: [
    // Proof area linked to this status panel
    'ref_proof',
  ],

  data: function () {
    return {
      // Display of current instruction
      instr: '',

      // Display of instruction number
      instr_no: '',
      
      // Display of status (text)
      status: '',

      // List of search results
      search_res: [],
    }
  },

  created() {
    this.Util = Util
  }
}
</script>