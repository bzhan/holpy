<template>
  <div id="app">
    <router-view />
  </div>
</template>

<script>
import 'bootstrap/dist/css/bootstrap.css'
import 'bootstrap-vue/dist/bootstrap-vue.css'

window.$ = require('jquery')


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

.keyword {
  font-weight: bold;
  color: #006000;
}

.indented-text {
  margin-left: 0.8em;
}

.item-text {
  font-family: Consolas, monospace;
  font-size: 15px;
}

.form-element {
  margin-left: 0.5em;
  padding-left: 5px;
  padding-right: 5px;
  font-size: 15px;
  font-family: Consolas, monospace;
}

textarea.form-element {
  vertical-align: top;
  resize: none;
  overflow: hidden;
}

.hint-element {
  margin-left: 0.7em;
  margin-right: 0.7em;
}

.ext-output {
  margin-top: 7px;
  margin-left: 10px;
}

</style>