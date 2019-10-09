<template>
  <div class="signinpanel">
    <form>
      <div class="form-group">
        <p style="margin-left:5px">Welcome to holpy</p>
        <input v-model="name" type="text" class="form-control" placeholder="username">
      </div>
      <div class="form-group">
        <input v-model="password" type="password" class="form-control" placeholder="password">
      </div>
      <button class="btn btn-primary" v-on:click.prevent="submit">Register</button>
    </form>
    <p>{{info}}</p>
  </div>
</template>

<script>
import axios from 'axios'

export default {
  name: 'Register',

  data: function () {
    return {
      name: '',
      password: '',
      info: '',
    }
  },
  
  methods: {
    submit: async function () {
      const data = {
        name: this.name,
        password: this.password
      }
      const response = await axios.post('http://127.0.0.1:5000/api/register_login', JSON.stringify(data))

      if (response.data.result === 'success') {
        this.info = ''
        this.$router.push({name: 'main'})
      } else {
        this.info = 'User already exists'
      }
    }
  }
}
</script>

<style scoped>

.signinpanel {
  width: 320px;
  margin: 10% auto 0 auto;
}

.signinpanel .btn {
  margin-top: 15px;
}

.signinpanel form {
  background: white;
  border: 1px solid rgba(255,255,255,.3);
  box-shadow: 0 3px 0 rgba(12, 12, 12, 0.03);
  border-radius: 3px;
  padding: 30px;
}

</style>
