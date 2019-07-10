var vm = new Vue({
    el: 'div#wrap',
    data: {
        text: '',
        com: '',
        pre: '',
        post: '',
        proof_very: ''
        },
    methods: {
        get_data: function() {
            axios({
                method: 'get',
                url: '/get_data',
                data: {}
            }).then(function(res) {
                vm.pre = res.data['pre'];
                vm.post = res.data['post'];
                vm.com = res.data['com'];
            })
        },
       process: function() {
            axios({
                method: 'post',
                url: '/program_verify',
                data: {
                    'com': this.com,
                    'pre': this.pre,
                    'post': this.post
                }
            }).then(function(res) {
                vm.text = res.data['very'];
                vm.proof_very = res.data['proof_very'];
            })
       }
    }
})