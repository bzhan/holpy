import Vue from 'vue'
import VueRouter from 'vue-router'

Vue.use(VueRouter)

import Index from './components/Index.vue'
import Login from './components/Login.vue'
import Register from './components/Register.vue'
import Editor from './components/Editor.vue'
import ProVerify from './components/ProVerify.vue'

const routes = [
  {path: '/', name: 'main', component: Index},
  {path: '/login', name: 'login', component: Login},
  {path: '/register', name: 'register', component: Register},
  {path: '/ide', name: 'editor', component: Editor},
  {path: '/program', name: 'program', component: ProVerify}
]

const router = new VueRouter({
  routes,
  mode: 'history'
})

export default router