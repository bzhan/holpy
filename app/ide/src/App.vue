<template>
  <div id="app">
    <router-view />
  </div>
</template>

<script>
import Main from './components/Main.vue'
import 'bootstrap/dist/css/bootstrap.css'
import 'bootstrap-vue/dist/bootstrap-vue.css'

import Util from './../static/js/util.js'
window.$ = require('jquery')

$(function () {
  $(document).on('input', '.form-element', function () {
    Util.adjust_input_size(this);
  });

  $(document).on('keydown', '.unicode-replace', function (e) {
    Util.replace_unicode(this, e);
  });
})


export default {
  name: 'app',
  components: {
    Main
  }
}
</script>

<style>
#app {
  font-family: 'Avenir', Helvetica, Arial, sans-serif;
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
  text-align: center;
  color: #2c3e50;
}
</style>
