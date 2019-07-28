// Interface for program verification.

var cells = {}

var vm = new Vue({
    el: 'div#wrap',
    data: {
        program: '', style_file: {background: '#F0F0F0'}, proof_content: '',
        proof_stat: '', file_data: [], proof_process: false, proof_init_stat: 'upcoming'
    },
    methods: {
        proof_init : function (data_relate) {
            axios({
                method: 'post',
                url: '/api/init-empty-proof',
                data: {
                    'com': data_relate['com'],
                    'pre': data_relate['pre'],
                    'post': data_relate['post'],
                    'prog_verify': 'true'
                }
            }).then(function (res) {
                var proof = res.data.proof;
                alert(proof);
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
                    vm.$options.methods.proof_init(data_relate);
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