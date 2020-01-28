<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">holpy</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click='new_file'>New</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='open_file'>Open</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='load_file'>Save</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='print_file'>Print</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Examples" left>
          <b-dropdown-item href="#" v-on:click=''>1.Top Ten</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>2.PWW</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>3.Jar</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>4.Pyth</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>5.Manual</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>6.GDD Full</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>7.Book</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Rulers</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Other</b-dropdown-item>
          
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Construct" left>
          <b-dropdown-item href="#" v-on:click=''>Point by Point and Segment</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Radical of Two Circles</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Oriented Segment</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Oriented T Segment</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Oriented Segment * Ratio</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Oriented T Segment * Ratio</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Proportional Segment</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Point</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Line</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Circle</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Action</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Polygon</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Special Angles</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Constraint" left>
          <b-dropdown-item href="#" v-on:click=''>Eqangle</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Eqangle3p</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Angle Specification</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Equal Ratio</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Equal Distance</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Ratio Distance</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>CCtangent</b-dropdown-item>
        </b-nav-item-dropdown>

        <b-nav-item-dropdown text="Action" left>
          <b-dropdown-item href="#" v-on:click=''>Trace</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Locus</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Animation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Full Polygon</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Measure Distance</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Arrow</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Equal Mark</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Right-angle Mark</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Calculation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Hide Object</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Show Object</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Transform</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Equivalence</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Free Transform</b-dropdown-item>
          
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Prove" left>
          <b-dropdown-item href="#" v-on:click=''>Prove</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>To Prove</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Numerical Check</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Polynomials</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>Nondegenerate Conditions</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click=''>All Solutions</b-dropdown-item>
          
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Lemmas" left>
          <b-dropdown-item href='#' v-on:click='rule_gdd'>Rules for GDD method</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click='rule_full_angle'>Rules for Full Angle method</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Option" left>
          <b-dropdown-item href='#' v-on:click=''>Preference</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Construct History</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Show Step Bar</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Style Dialog</b-dropdown-item>
        
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Help" left>
          <b-dropdown-item href='#' v-on:click=''>Help</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Online Help</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Help on Mode</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>HomePage</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Contact Us</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>Check for Update</b-dropdown-item>
          <b-dropdown-item href='#' v-on:click=''>About JGEX</b-dropdown-item>
          
        </b-nav-item-dropdown>
        
      </b-navbar-nav>
    </b-navbar>
    <div id="theory-list" v-show="ref_proof === undefined">
      <Content v-if="filelist !== undefined"
               v-bind:filelist="filelist"
               v-on:select-theory="onSelectTheory"
               ref="content"/>
    </div>
    <div id="proof-context" v-show="ref_proof !== undefined">
      <ProofContext v-bind:ref_proof="ref_proof" ref="context"/>
    </div>
    <div id="theory-content">
      <Theory v-bind:theory="theory"
              v-bind:ref_status="ref_status"
              v-bind:ref_context="ref_context"
              :editor="editor"
              v-on:set-message="onSetMessage"
              v-on:set-proof="handle_set_proof"
              v-on:query="handle_query"
              v-on:goto-link="handleGoToLink"
              ref="theory"/>
    </div>
    <div id="message" v-show="ref_proof === undefined">
      <Message v-bind:message="message" ref="message"/>
    </div>
    <div id="status" v-show="ref_proof !== undefined && query === undefined">
      <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>
    </div>
    <div id="query" v-show="ref_proof !== undefined && query !== undefined">
      <ProofQuery v-bind:query="query"
                  v-on:query-ok="handle_query_ok"
                  v-on:query-cancel="handle_query_cancel"/>
    </div>
  </div>
</template>



<style scoped>

#theory-list, #proof-context {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 48px;
  bottom: 0px;
  left: 0px;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 5px;
}

#theory-content {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#message, #status, #query {
  display: inline-block;
  width: 75%;
  height: 30%;
  left: 25%;
  position: fixed;
  top: 70%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

</style>
