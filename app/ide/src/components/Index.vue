<template>
  <div style="margin:10px">
    <h3>Directory</h3>
    <ul>
      <li><router-link :to="{name: 'editor'}">Edit theories</router-link></li>
      <li><router-link :to="{name: 'program'}">Program verification</router-link></li>
    </ul>
  </div>
</template>
