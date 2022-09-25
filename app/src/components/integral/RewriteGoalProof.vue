<template>
    <div>
      <span class="math-text">by rewrite goal</span>
      <span v-if="item.finished" class="math-text" style="color: green">&nbsp;(finished)</span><br/>
      <span class="math-text">{{label}}1.</span>&nbsp;
      <span class="math-text">Proof: </span>
      <Calculation v-bind:item="item.start" v-bind:label="label + '1.'"
                   v-bind:selected_item="selected_item"
                   v-bind:selected_facts="selected_facts"
                   v-bind:is_rewrite_goal_proof="true"
                   @select="(lbl) => $emit('select', lbl)"/>
    </div>
  </template>
  
  <script>
  import Calculation from './Calculation.vue'
  
  export default {
    name: "RewriteGoalProof",
    components: {
      Calculation,
    },
  
    props: [
      "item",
      "label",
      "selected_item",
      "selected_facts",
    ]
  }
  
  </script>
  