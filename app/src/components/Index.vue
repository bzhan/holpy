<template>
  <div style="margin:10px">
    <p v-if="$state.user">Logged in as {{$state.user}}</p>
    <p v-else>Not logged in</p>
    <h3>Directory</h3>
    <ul>
      <li><router-link :to="{name: 'login'}">Login</router-link></li>
      <li><router-link :to="{name: 'register'}">Register</router-link></li>
      <li><router-link :to="{name: 'editor'}">Edit theories</router-link></li>
      <li><router-link :to="{name: 'program'}">Program verification</router-link></li>
      <li><router-link :to="{name: 'integral'}">Integral</router-link></li>
      <li><router-link :to="{name: 'monitor'}">Check theories</router-link></li>
      <li><router-link :to="{name: 'geometry'}">Geometry</router-link></li>
      <li><a href="#" v-on:click="$state.user = null">Logout</a></li>
    </ul>
  </div>
</template>
