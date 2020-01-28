import Vue from 'vue'
import VueRouter from 'vue-router'

Vue.use(VueRouter)

import Index from './components/Index.vue'
import Login from './components/login/Login.vue'
import Register from './components/login/Register.vue'
import Editor from './components/Editor.vue'
import ProVerify from './components/ProVerify.vue'
import Monitor from './components/Monitor.vue'
import Integral from './components/Integral.vue'
import Geometry from './components/geometry/Geometry.vue'

const routes = [
  {path: '/', name: 'main', component: Index},
  {path: '/login', name: 'login', component: Login},
  {path: '/register', name: 'register', component: Register},
  {path: '/ide', name: 'editor', component: Editor},
  {path: '/program', name: 'program', component: ProVerify},
  {path: '/integral', name: 'integral', component: Integral},
  {path: '/monitor', name: 'monitor', component: Monitor},
  {path: '/geometry', name: 'geometry', component: Geometry}
]

const router = new VueRouter({
  routes,
  mode: 'history'
})

export default router
