<template>
  <span class="item-text">
    <span v-for="(p, index) in line" v-bind:key="index"
          v-bind:style="{color: get_color(p[1])}">{{p[0].replace(/ /g, '&nbsp;')}}</span>
  </span>
</template>

<script>
export default {
  name: 'Expression',
  props: [
    "line"
  ],

  methods: {
    get_color: function (x) {
      if (x === 0) { // normal
        return 'black'
      } else if (x === 1) {  // bound
        return '#006000'
      } else if (x === 2) { // var
        return 'blue'
      } else if (x === 3) { // tvar
        return 'purple'
      } else if (x === 4) {
        return 'silver'
      }
    }
  }
}
</script>
