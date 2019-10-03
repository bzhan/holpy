import Vue from 'vue'
import VueRouter from 'vue-router'

Vue.use(VueRouter)

import Main from './components/Main.vue'

const routes = [
    {path: '/ide', name: 'main', component: Main}
]

const router = new VueRouter({
    routes,
    mode: 'history'
})

export default router
