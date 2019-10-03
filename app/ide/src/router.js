import Vue from 'vue'
import VueRouter from 'vue-router'

Vue.use(VueRouter)

import Main from './components/Main.vue'
import ProVerify from './components/ProVerify.vue'

const routes = [
    {path: '/ide', name: 'main', component: Main},
    {path: '/program', name: 'program', component: ProVerify}
]

const router = new VueRouter({
    routes,
    mode: 'history'
})

export default router
