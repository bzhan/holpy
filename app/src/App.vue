<template>
  <div id="app">
    <router-view />
  </div>
</template>

<script>
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
  }
}
</script>

<style>

.navbar {
  padding: 4px 1rem;
}

.dropdown-menu.show {
  margin: 3px 0px;
  padding: 0px
}

a.dropdown-item {
  padding: 0.3rem 1.0rem 0.3rem 0.5rem;
}

.CodeMirror {
  height: 260px;
}
</style>