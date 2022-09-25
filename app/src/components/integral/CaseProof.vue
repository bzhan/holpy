<template>
    <div>
      <span class="math-text">split by &nbsp;&nbsp;</span>
      <MathEquation v-bind:data="'\\(' + item.split_cond + '\\)'"/><br/>
      <span class="math-text">{{label}}1. Case 1: </span>
      <span @click="$emit('select', label + '1.')"
            :class="{selected: selected_item == label + '1.'}">
        <MathEquation v-bind:data="'\\(' + item.case_1.latex_goal + '\\)'"/>
      </span>
      <span v-if="'conds' in item.case_1 && item.case_1.conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in item.case_1.conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
      </span><br/>
      <CalculationProof v-if="'proof' in item.case_1 && item.case_1.proof.type === 'CalculationProof'"
                        v-bind:item="item.case_1.proof" v-bind:label="label + '1.'"
                        v-bind:selected_item="selected_item"
                        v-bind:selected_facts="selected_facts"
                        @select="(lbl) => $emit('select', lbl)"/>
      <RewriteGoalProof v-if="'proof' in item.case_1 && item.case_2.proof.type === 'RewriteGoalProof'"
                        v-bind:item="item.case_1.proof" v-bind:label="label + '1.'"
                        v-bind:selected_item="selected_item"
                        v-bind:selected_facts="selected_facts"
                        @select="(lbl) => $emit('select', lbl)"/>
      <span class="math-text">{{label}}2. Case 2: </span>
      <span @click="$emit('select', label + '2.')"
            :class="{selected: selected_item == label + '2.'}">
        <MathEquation v-bind:data="'\\(' + item.case_2.latex_goal + '\\)'"/>
      </span>
      <span v-if="'conds' in item.case_2 && item.case_2.conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in item.case_2.conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
      </span><br/>
      <CalculationProof v-if="'proof' in item.case_2 && item.case_2.proof.type === 'CalculationProof'"
                        v-bind:item="item.case_2.proof" v-bind:label="label + '2.'"
                        v-bind:selected_item="selected_item"
                        v-bind:selected_facts="selected_facts"
                        @select="(lbl) => $emit('select', lbl)"/>
      <RewriteGoalProof v-if="'proof' in item.case_2 && item.case_2.proof.type === 'RewriteGoalProof'"
                        v-bind:item="item.case_2.proof" v-bind:label="label + '2.'"
                        v-bind:selected_item="selected_item"
                        v-bind:selected_facts="selected_facts"
                        @select="(lbl) => $emit('select', lbl)"/>
    </div>
  </template>
  
  <script>
  import MathEquation from '../util/MathEquation.vue'
  import CalculationProof from './CalculationProof.vue'
  import RewriteGoalProof from './RewriteGoalProof.vue'
  export default {
    name: "CaseProof",
    components: {
      MathEquation,
      CalculationProof,
      RewriteGoalProof,
    },
  
    props: [
      "item",
      "label",
      "selected_item",
      "selected_facts",
    ]
  }
  
  </script>
  