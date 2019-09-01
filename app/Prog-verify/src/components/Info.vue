<template>
    <div class="rbottom" style="overflow: auto;">
      <div id="prf" name="addition" class="selected">
        <div class="output-wrapper">
          <div class="output">
            <pre>{{ status }}</pre>
            <div class="ouputwrapper">
              <div id="output-instr">
                <a href="#" id="link-backward" style="float:left;margin-left:20pt">&lt;</a>
                <span id="instruction-number" style="float:left;display:inline-block;width:30pt;text-align:center">
                  {{ instr_no }}
                </span>
                <a href="#" id="link-forward" style="float:left;">&gt;</a>
                <span id="instruction" style="float:left;margin-left:10pt">
                  {{ instr }}
                </span>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
</template>

<script>
export default {
  name: 'Info',
  props: ['instr_no', 'instr', 'status', 'color'],
  data: function() {
    return {
      styleSta: {color: ''}
    }
  },
  methods: {
    display_running() {
      this.display_status('Running')
    }
  },
  watch: {
    status: function (val) {
      var statusOutput = document.querySelector('.rbottom .selected .output pre')
      statusOutput.innerHTML = val
      statusOutput.style.color = this.color
    }
  }
}
</script>

<style scoped>

</style>
