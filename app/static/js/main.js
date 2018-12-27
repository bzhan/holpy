(function ($) {
    var instructions = [];
    var pageNum = 0;
    var index = 0;
    var theorem = {};
    var cells = {};

    $(document).ready(function () {
        $('#theorem-select').ready(function () {
            $(document).ready(function () {
                var event = {'event': 'init_theorem'};
                var data = JSON.stringify(event);

                $.ajax({
                    url: "/api/init",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        theorem = result;
                        for (var i in result) {
                            $('#theorem-select').append(
                                $('<option>' + i + '</option>')
                            )
                        }
                        $('#theorem-select').selectpicker('refresh');
                    }
                })
            });
        });

        $('#add-cell').on('click', function () {
            pageNum++;
            // Add CodeMirror textarea
            id = 'code' + pageNum + '-pan';
            $('#codeTab').append(
                $('<li class="nav-item"><a  class="nav-link" ' +
                    'data-toggle="tab"' +
                    'href="#code' + pageNum + '-pan">' +
                    'Page ' + pageNum +
                    '<button id="close_tab" type="button" ' +
                    'title="Remove this page">×</button>' +
                    '</a></li>'));
            let class_name = 'tab-pane fade active newCodeMirror code-cell';
            if (pageNum === 1)
                class_name = 'tab-pane fade in active code-cell';
            $('#codeTabContent').append(
                $('<div class="' + class_name + '" id="code' + pageNum + '-pan">' +
                    '<label for="code' + pageNum + '"></label> ' +
                    '<textarea' + ' id="code' + pageNum + '""></textarea>'));
            init_editor("code" + pageNum);
            // Add location for displaying results
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div></div>'));
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<a href="#" id="link-left" style="float:left;"><</a><pre id="instruction" style="float:left;"> </pre>'
                    +'<a href="#" id="link-right" style="float:left;">></a></div></div>'));

            $('#codeTab a[href="#code' + pageNum + '-pan"]').tab('show');
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active')
            });
        });

        $('#right').on('click', '#link-left', function () {
            if (index < instructions.length-1) {
                index++;
                var status_output = get_selected_instruction();
                status_output.innerHTML = instructions[index];
            }
        })

        $('#right').on('click', '#link-right', function () {
            if (index > 0) {
                index--;
                var status_output = get_selected_instruction();
                status_output.innerHTML = instructions[index];
            }
        })
 
        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            $(this).tab('show');

        });

        $('#codeTab').on('shown.bs.tab', 'a', function (event) {
            var editor = document.querySelector('.code-cell.active textarea + .CodeMirror').CodeMirror;
            var rtop = document.querySelector('.rtop');
            editor.focus();
            editor.setCursor(editor.lineCount(), Number.MAX_SAFE_INTEGER);
            editor.setSize("auto", rtop.clientHeight - 40);
            editor.refresh();
        });

        $('#codeTab').on('click', ' li a #close_tab', function () {
            if ($('#codeTab').children().length === 1)
                return true;
            else {
                var tabId = $(this).parents('li').children('a').attr('href');
                var pageNum = $(this).parents('li').children('a')[0].childNodes[0].nodeValue;
                var first = false;
                $(this).parents('li').remove('li');
                $(tabId).remove();
                if (pageNum === "Page 1")
                    first = true;
                remove_page(first);
                $('#codeTab a:first').tab('show');
            }
        });

        function remove_page(first) {
            if (first)
                pageNum = 0;
            else
                pageNum = 1;
            $('#codeTab > li').each(function () {
                var pageId = $(this).children('a').attr('href');
                if (pageId === "#code1-pan") {
                    return true;
                }
                pageNum++;
                $(this).children('a').html('Page ' + pageNum +
                    '<button id="close_tab" type="button" ' +
                    'title="Remove this page">×</button>');
            });
        }

        $('#delete-cell').on('click', function () {
            $('.code-cell.selected').remove();
        });

        $('#introduction').on("click", function () {
            introduction(get_selected_editor());
        });

        $('#add-line-after').on("click", function () {
            add_line_after(get_selected_editor());
        });

        $('#apply-backward-step').on("click", function () {
            apply_backward_step(get_selected_editor());
        });

        $('#apply-induction').on("click", function () {
            apply_induction(get_selected_editor());
        });

        $('#rewrite-goal').on("click", function () {
            rewrite_goal(get_selected_editor());
        });

        $('#init-button').on("click", function () {
            let variables_area = document.querySelector('#variables .CodeMirror').CodeMirror;
            let assumes_area = document.querySelector('#assumes .CodeMirror').CodeMirror;
            let conclusions_area = document.querySelector('#conclusions .CodeMirror').CodeMirror;
            var variables = [];
            var assumes = [];
            var conclusion = undefined;
            var reg_blank = /^\s*$/g;
            variables_area.eachLine(line => {
                if (!reg_blank.test(line.text)) {
                    variables.push(line.text)
                }
            });
            assumes_area.eachLine(line => {
                if (!reg_blank.test(line.text)) {
                    assumes.push(line.text)
                }
            });
            conclusions_area.eachLine(line => {
                if (!reg_blank.test(line.text)) {
                    conclusion = line.text
                }
            });
            $(document).ready(function () {
                var event = {
                    'event': 'init_cell',
                    'id': get_selected_id(),
                    'variables': variables,
                    'assumes': assumes,
                    'conclusion': conclusion
                };
                var data = JSON.stringify(event);

                $.ajax({
                    url: "/api/init",
                    type: "POST",
                    data: data,
                    success: display_checked_proof
                });
            });
        });

        $('#add-cell').click();
        $('.code-cell').addClass('selected');

        get_selected_editor().focus();

        document.getElementById('open-file').addEventListener('change', function (e) {
            e = e || window.event;

            let files = this.files;
            let editor = get_selected_editor();
            editor.setValue("");
            let i = 0, f;
            for (; f = files[i]; i++) {
                let reader = new FileReader();
                reader.onload = (function (file) {
                    return function (e) {
                        editor.setValue(editor.getValue() + this.result);
                    };
                })(f);
                reader.readAsText(f);
            }
        });

        document.getElementById('open-problem').addEventListener('change', function (e) {
            e = e || window.event;

            let files = this.files;
            let i = 0, f;
            if (files !== '') {
                for (; f = files[i]; i++) {
                    let reader = new FileReader();
                    reader.onload = (function () {
                        var json_data = JSON.parse(this.result);
                        instructions = json_data['instructions'];
                        var event = {
                            'event': 'init_cell',
                            'id': get_selected_id(),
                            'variables': json_data['variables'],
                            'assumes': json_data['assumes'],
                            'conclusion': json_data['conclusion']
                        };
                        var data = JSON.stringify(event);
                        display_running();

                        $.ajax({
                            url: "/api/init",
                            type: "POST",
                            data: data,
                            success: function (result) {
                                display_checked_proof(result);
                                get_selected_editor().focus();
                                display_instuctions(instructions);
                            }
                        });
                    });
                    reader.readAsText(f);
                }
            }
            $('#open-problem')[0].value = '';
        });

        function rp(x) {
            if (x === 0)
                return 'normal';
            if (x === 1)
                return 'bound';
            if (x === 2)
                return 'var';
        }

        document.getElementById('open-json').addEventListener('change', function (e) {
            e = e || window.event;

            let files = this.files;
            let i = 0, f;
            if (files !== '') {
                for (; f = files[i]; i++) {
                    let reader = new FileReader();
                    reader.onload = (function () {
                        var json_data = JSON.parse(this.result);
                        var data = JSON.stringify(json_data);

                        $.ajax({
                            url: "/api/json",
                            type: "POST",
                            data: data,
                            success: function (result) {
                                $('#left').empty();
                                for (var d in result['data']) {
                                    var name = result['data'][d]['name'];
                                    var obj = result['data'][d]['prop'];
                                    var ty = result['data'][d]['ty'];
                                    var str = ''

                                    if (ty === 'def.ax'){
                                        $('#left').append($('<p><font color="#006000"><b>constant</b></font> ' + name + ' :: ' + obj +'</p>'))
                                    }

                                    if (ty === 'thm'){
                                    $.each(obj, function(i, val) {
                                        str = str +'<tt class="'+rp(val[1])+'">'+val[0]+'</tt>';
                                    })
                                    $('#left').append($('<p><font color="#006000"><b>theorem</b></font> ' + name + ':&nbsp;<a href="#">proof</a></br>&nbsp;&nbsp;&nbsp;'+str+'</p>'));
                                    }

                                    if (ty === 'type.ind'){
                                        var constrs = result['data'][d]['constrs'];
                                        str = '</br>' + constrs[0]['name'] + '</br>' + constrs[1]['name']
                                        for (var i in constrs[1]['args']){
                                            str += ' (' + constrs[1]['args'][i] + ' :: '+ obj[i] + ')';
                                        }
                                    $('#left').append($('<p><font color="#006000"><b>datatype</b></font> ' + constrs[0]['type'] + ' =' + str + '</p>'));
                                    }

                                    if (ty === 'def.ind'){
                                    $('#left').append($('<p id="fun'+j+'"><font color="#006000"><b>fun</b></font> ' + name + ' :: ' + result['data'][d]['type']
                                            + ' where'+'</p>'))
                                        for (var j in obj){
                                            str = ''
                                            $.each(obj[j], function(i, val){
                                                str = str + '<tt class="'+ rp(val[1]) + '">' +val[0] +'</tt>';
                                            })
                                            $('#left p').last().append($('<p>'+ str+'</p>'));
                                         }

                                    }

                                }
                            }
                        });
                    });
                    reader.readAsText(f);
                }
            }
            $('#open-json')[0].value = '';
        });

        $('#left').on('click', 'a', function(){
            $('#add-cell').click();
            $('#init-button').click();
        })

        document.getElementById("run-button").addEventListener('click', send_input);
    });

    function init_editor(editor_id = "code1") {
        var editor = CodeMirror.fromTextArea(document.getElementById(editor_id), {
            mode: "text/x-python",
            lineNumbers: true,
            theme: "",
            lineWrapping: true,
            foldGutter: true,
            smartIndent: false,
            matchBrackets: true,
            viewportMargin: Infinity,
            scrollbarStyle: "overlay",
            extraKeys: {
                "Ctrl-I": introduction,
                "Ctrl-B": apply_backward_step,
                "Ctrl-R": rewrite_goal,
            }
        });
        var rtop = document.querySelector('.rtop');
        editor.setSize("auto", rtop.clientHeight - 40);
        editor.setValue("");
        editor.on("keydown", function (cm, event) {
            let line_no = cm.getCursor().line;
            let line = cm.getLine(line_no);

            if (event.ctrlKey && event.code === 'Enter') {
                event.preventDefault();
                send_input();
            } else if (event.code === 'Enter') {
                event.preventDefault();
                add_line_after(cm);
            } else if (event.code === 'Tab') {
                event.preventDefault();
                unicode_replace(cm);
            } else if (event.code === 'Backspace') {
                if (line.endsWith(": ")) {
                    event.preventDefault();
                    remove_line(cm);
                }
            }
        });
        editor.on("focus", function (cm, event) {
            $('#codeTabContent .code-cell').each(function () {
                $(this).removeClass('selected');
            });
            $(cm.getTextArea().parentNode).addClass('selected');
            set_theorem_select(cm);
        });

        editor.on("cursorActivity", function (doc) {
            console.log(doc);
            set_read_only(doc);
        })
    }

    function set_theorem_select(doc) {
        $('#theorem-select').empty();
        for (var i in theorem) {
            $('#theorem-select').append(
                $('<option>' + i + '</option>')
            )
        }
        let lines = [];
        doc.eachLine(function (line) {
            if (line.text.startsWith("var"))
                lines.push(line.text);
        });
        for (var i = lines.length - 1; i >= 0; i--) {
            $('#theorem-select option:first-child').before(
                $('<option>' + lines[i] + '</option>')
            )
        }
        $('#theorem-select').selectpicker('refresh');
    }

    function set_read_only(doc) {

    }

    function resize_editor() {
        var editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
        var rtop = document.querySelector('.rtop');
        editor.setSize("auto", rtop.clientHeight - 40);
        editor.refresh();
    }

    Split(['.rtop', '.rbottom'], {
        sizes: [40, 60],
        direction: 'vertical',
        minSize: 39,
        onDrag: resize_editor,
        gutterSize: 2,
    });
    Split(['.left', '.right'], {
        sizes: [20, 80],
        gutterSize: 2,
    });
})(jQuery);
