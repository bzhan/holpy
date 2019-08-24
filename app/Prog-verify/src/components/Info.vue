<template>
    <div class="rbottom" style="overflow: auto;">
      <div id="prf" name="addition" class="selected">
        <div class="output-wrapper">
          <div class="output">
            <pre>{{ ststus }}</pre>
            <div class="ouputwrapper">
            </div>
          </div>
        </div>
      </div>
    </div>
</template>

<script>
export default {
  name: 'Info',
  data: function() {
    return {
      status: '',
      styleSta: {color: ''}
    }
  },
  methods: {
    display_ststus: function (status, color = '') {
      this.status = status
      this.styleSta.color = color
    },
    display_running() {
      this.display_ststus('Running')
    }
  }
}
</script>

<style scoped>

</style>
