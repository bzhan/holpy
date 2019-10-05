<template>
  <div id="app">
    <router-view />
  </div>
</template>

<script>
import Editor from './components/Editor.vue'
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
    Editor
  }
}
</script>
