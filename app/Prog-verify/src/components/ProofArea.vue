<template>
  <div class="tab-pane fade active code-cell">
    <label :for=page_num></label>
    <textarea :id=page_num></textarea>
    <br>
    <label>{{proof}}</label>
  </div>
</template>

<script>
export default {
  name: 'ProofArea',
  props: ['page_num', 'proof'],
  data: function () {
    return {
      text: "proof"
    }
  }
}
</script>
