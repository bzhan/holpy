
var vm = new Vue({
    el: 'div#wrap',
    data: {
        text: '', com: '', style_file: {background: '#F0F0F0'},
        pre: '', post: '', proof_very: '', file_data: []
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
       data_process: function(e) {
            var num = e.currentTarget.children[0].name;
            num = Number(num);
            var data_relate = this.file_data[num];
            axios({
                method: 'post',
                url: '/program_verify',
                data: {
                    'com': data_relate['com'],
                    'pre': data_relate['pre'],
                    'post': data_relate['post']
                }
            }).then(function(res) {
                vm.text = res.data['very'];
                vm.proof_very = res.data['proof_very'];
            })
       },
       button_change: function() {
            this.style_file.background = 'white';
       },
       button_recover: function() {
            this.style_file.background = '#F0F0F0';
       },
       get_file: function(e) {
            var file_name = e.target.files[0].name;
            axios({
                method: 'post',
                url: '/api/get_file',
                data: {'file_name' : file_name}
            }).then(function(res) {
                vm.file_data = res.data['file_data'];
            })
       }
    }
})