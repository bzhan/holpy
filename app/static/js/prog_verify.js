// Interface for program verification.

var vm = new Vue({
    el: 'div#wrap',
    data: {
        program: '', com: '', style_file: {background: '#F0F0F0'}, proof_content: '',
        pre: '', post: '', proof_stat: '', file_data: [], proof_process: false
    },
    methods: {
        get_data: function () {
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
        data_process: function (e) {
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
            }).then(function (res) {
                vm.program = res.data['program'];
                vm.proof_stat = res.data['proof_stat'][0];
                var failure_num = Number(res.data['proof_stat'][1]);
                if (failure_num != 0) {
                    vm.proof_process = true;
                }
                else {
                    vm.proof_process = false;
                }
            })
       },
       button_change: function () {
            this.style_file.background = 'white';
       },
       button_recover: function () {
            this.style_file.background = '#F0F0F0';
       },
       get_file: function (e) {
            var file_name = e.target.files[0].name;
            axios({
                method: 'post',
                url: '/api/get_file',
                data: {'file_name' : file_name}
            }).then(function (res) {
                vm.file_data = res.data['file_data'];
            })
       }
    }
})