import Vue from 'vue'
import Router from 'vue-router'
import ProVerify from '@/components/ProVerify'

Vue.use(Router)

export default new Router({
  routes: [
    {
      path: '/',
      name: 'ProVerify',
      component: ProVerify
    }
  ]
})
