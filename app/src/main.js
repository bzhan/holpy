import Vue from 'vue'
import App from './App.vue'
import BootstrapVue from 'bootstrap-vue'
import 'bootstrap/dist/css/bootstrap.css'
import 'bootstrap-vue/dist/bootstrap-vue.css'

Vue.use(BootstrapVue)

import 'vue-awesome/icons'
import Icon from 'vue-awesome/components/Icon'
Vue.component('v-icon', Icon)

import Expression from './components/Expression'
Vue.component('Expression', Expression)

import router from './router'

Vue.config.productionTip = false

import state from './state'

Object.defineProperty(Vue.prototype, '$state', {
  get: () => state
})

new Vue({
  data: state,
  router,
  render: h => h(App),
}).$mount('#app')
