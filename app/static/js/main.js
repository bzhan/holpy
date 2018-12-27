(function ($) {
    var instructions = [];
    var pageNum = 0;
    var index = 0;
    var theorem = {};
    var replace_obj = {
        "\\lambda": "λ",
        "%": "λ",
        "\\forall": "∀",
        "\\exists": "∃",
        "\\and": "∧",
        "&": "∧",
        "\\or": "∨",
        "|": "∨",
        "-->": "⟶",
        "~": "¬",
        "\\not": "¬",
        "=>": "⇒"
    }

    function get_selected_id() {
        return document.querySelector('.code-cell.selected textarea').id;
    }

    function get_selected_editor() {
        return document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
    }

    function get_selected_output() {
        return document.querySelector('.code-cell.selected .output pre');
    }

    function get_display_ouput() {
        return document.querySelector('#instruction');
    }

    function display_running() {
        var status_output = get_selected_output();
        status_output.innerHTML = "Running";
    }

    function display_checked_proof(result) {
        var editor = get_selected_editor();
        var status_output = get_selected_output();

        if ("failed" in result) {
            status_output.innerHTML = result["failed"] + ": " + result["message"]
        } else {
            editor.setValue(result["proof"]);
            var num_gaps = result["report"]["num_gaps"];
            if (num_gaps > 0) {
                status_output.innerHTML = "OK. " + num_gaps + " gap(s) remaining."
            } else {
                status_output.innerHTML = "OK. Proof complete!"
            }
        }
    }

    function display_instuctions(instructions) {
        var status_output = get_display_ouput();
        status_output.innerHTML = instructions[0];
    }

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
            // pageNum++;
            // // Add CodeMirror textarea
            // id = 'code' + pageNum + '-pan';
            // $('#codeTabContent').append(
            //     $('<div class="code-cell" id=' + id + '>' +
            //         '<label for="code' + pageNum + '"></label> ' +
            //         '<textarea' + ' id="code' + pageNum + '""></textarea></div>'));
            // init_editor("code" + pageNum);
            // // Add location for displaying results
            // $('#' + id).append(
            //     $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
            //         '<pre> </pre></div></div>'));
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
                var status_output = get_display_ouput();
                status_output.innerHTML = instructions[index];
            }
        })

        $('#right').on('click', '#link-right', function () {
            if (index > 0) {
                index--;
                var status_output = get_display_ouput();
                status_output.innerHTML = instructions[index];
            }
        })
 
        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            $(this).tab('show');
        });

        $('#codeTab').on('click', ' li a #close_tab', function () {
            if ($('#codeTab').children().length === 1)
                return true;
            else {
                var tabId = $(this).parents('li').children('a').attr('href');
                var pageNum = $(this).parents('li').children('a').childNodes[0].nodeValue;
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

        init_input_box('variables');
        init_input_box('assumes');
        init_input_box('conclusions');
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
            if (x===0)
                return  'normal';
            if (x===1)
                return  'bound';
            if (x===2)
                return  'var';
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
                                    var obj_list = result['data'][d]['prop'];
                                    var str = ''
                                    $.each(obj_list, function(i, val) {
                                        str = str+'<tt class="'+rp(val[1])+'">'+val[0]+'</tt>';
                                    })
                                    $('#left').append($('<p><font color="#006000"><b>theorem</b></font> '+name+':</br>&nbsp;&nbsp;&nbsp;'+str+'</p>'));
                                }
                            }
                        });
                    });
                    reader.readAsText(f);
                }
            }
            $('#open-json')[0].value = '';
        });

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
            scrollbarStyle: "overlay",
            extraKeys: {
                "Ctrl-I": introduction,
                "Ctrl-B": apply_backward_step,
                "Ctrl-R": rewrite_goal,
            }
        });
        editor.setSize("auto", "auto");
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
            // get_cell_state();
        });
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

    function send_input() {
        $(document).ready(function () {
                var editor = get_selected_editor();
                var line_no = editor.getCursor().line;
                var input = {
                    "id": get_selected_id(),
                    "proof": editor.getValue()
                };
                var data = JSON.stringify(input);
                display_running();

                $.ajax({
                    url: "/api/check-proof",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        display_checked_proof(result);
                        editor.setCursor(line_no, Number.MAX_SAFE_INTEGER);
                    }
                })
            }
        )
    }

    function add_line_after(cm) {
        $(document).ready(function () {
                var line_number = cm.getCursor().line;
                var line = cm.getLine(line_number);
                var input = {
                    "id": get_selected_id(),
                    "line": line,
                };
                var data = JSON.stringify(input);
                display_running();

                $.ajax({
                    url: "/api/add-line-after",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        display_checked_proof(result);
                        cm.setCursor(line_number + 1, Number.MAX_SAFE_INTEGER);
                    }
                })
            }
        )
    }

    function remove_line(cm) {
        $(document).ready(function () {
            var line_number = cm.getCursor().line;
            var line = cm.getLine(line_number);
            var input = {
                "id": get_selected_id(),
                "line": line,
            };
            var data = JSON.stringify(input);
            display_running();

            $.ajax({
                url: "/api/remove-line",
                type: "POST",
                data: data,
                success: function (result) {
                    display_checked_proof(result);
                    cm.setCursor(line_number - 1, Number.MAX_SAFE_INTEGER);
                }
            })
        })
    }

    function introduction(cm) {
        $(document).ready(function () {
            var line_number = cm.getCursor().line;
            var line = cm.getLine(line_number);
            var input = {
                "id": get_selected_id(),
                "line": line,
            };

            if (line.indexOf("⊢ ∀") !== -1) {
                input["var_name"] = prompt('Enter variable name').split(",")
            }
            var data = JSON.stringify(input);
            display_running();

            $.ajax({
                url: "/api/introduction",
                type: "POST",
                data: data,
                success: function (result) {
                    display_checked_proof(result);
                    cm.setCursor(line_number + result['line-diff'], Number.MAX_SAFE_INTEGER);
                }
            })
        })
    }

    function apply_backward_step(cm) {
        var line_number = cm.getCursor().line;
        var line = cm.getLine(line_number);
        swal({
            title: 'Please enter the theorem used',
            html:
                '<input id="swal-input1" class="swal2-input">' +
                '<select id="swal-input2" class="swal2-select"></select>',
            onOpen: function () {
                init_select_abs()
            },
            showCancelButton: true,
            confirmButtonText: 'confirm',
            showLoaderOnConfirm: true,
            preConfirm: () => {
                var data = {
                    'id': get_selected_id(),
                    'line': line,
                    'theorem': document.getElementById('swal-input1').value,
                };
                return fetch('/api/apply-backward-step', {
                        method: 'POST', // or 'PUT'
                        body: JSON.stringify(data),
                        headers: {
                            headers: {
                                'Accept': 'application/json',
                                'Content-Type': 'application/json',
                            },
                        },
                    }
                ).then(response => {
                    if (!response.ok) {
                        throw new Error(response.statusText)
                    }
                    return response.json()
                })
                    .catch(error => {
                        swal.showValidationMessage(
                            `Request failed: ${error}`
                        )
                    })
            },
            allowOutsideClick:
                () => !swal.isLoading()
        }).then((result) => {
            if (result) {
                display_checked_proof(result['value']);
            }
        })
    }

    function apply_induction(cm) {
        $(document).ready(function () {
            var line_no = cm.getCursor().line;
            var line = cm.getLine(line_no);
            var input = {
                'id': get_selected_id(),
                'line': line
            };

            input['theorem'] = prompt('Enter induction theorem and variable name')
            var data = JSON.stringify(input);
            display_running();

            $.ajax({
                url: "/api/apply-induction",
                type: "POST",
                data: data,
                success: function (result) {
                    display_checked_proof(result);
                }
            })
        })
    }

    function rewrite_goal(cm) {
        $(document).ready(function () {
            var line_no = cm.getCursor().line;
            var line = cm.getLine(line_no);
            var input = {
                'id': get_selected_id(),
                'line': line
            };

            input['theorem'] = prompt('Enter rewrite theorem')
            var data = JSON.stringify(input);
            display_running();

            $.ajax({
                url: "/api/rewrite-goal",
                type: "POST",
                data: data,
                success: function (result) {
                    display_checked_proof(result);
                }
            })
        })
    }

    function unicode_replace(cm) {
        $(document).ready(function () {
            var cur_position = cm.getCursor()
            var line_number = cur_position.line
            var position = cur_position.ch
            var stri = cm.getRange({line: line_number, ch: 0}, cm.getCursor());
            for (var key in replace_obj) {
                l = key.length;
                if (stri.slice(-l) === key) {
                    start_position = {line: line_number, ch: position - l};
                    cm.replaceRange(replace_obj[key], start_position, cur_position);
                }
            }
        })
    }

    function init_select_abs() {
        $(document).ready(function () {
            var event = {
                "event": "init_theorem_abs",
            };
            var data = JSON.stringify(event);

            $.ajax({
                url: "/api/init",
                type: "POST",
                data: data,
                success: function (result) {
                }
            })
        })
    }

    function get_cell_state() {
        $(document).ready(function () {
            let variables_area = document.querySelector('#variables .CodeMirror').CodeMirror;
            let assumes_area = document.querySelector('#assumes .CodeMirror').CodeMirror;
            let conclusions_area = document.querySelector('#conclusions .CodeMirror').CodeMirror;
            variables_area.setValue('');
            assumes_area.setValue('');
            conclusions_area.setValue('');
            var event = {
                'id': get_selected_id(),
            };
            var data = JSON.stringify(event);

            $.ajax({
                url: "/api/get-cell-state",
                type: "POST",
                data: data,
                success: function (result) {
                    if (JSON.stringify(result) !== '{}') {
                        variables_area.setValue(result['variables'].join('\n'));
                        assumes_area.setValue(result['assumes'].join('\n'));
                        conclusions_area.setValue(result['conclusion']);
                    }
                }
            });
        });
    }

    function init_input_box(id) {
        let input_box = CodeMirror(document.getElementById(id), {
            mode: "text/x-python",
            lineNumbers: true,
            theme: "",
            lineWrapping: true,
            foldGutter: true,
            smartIndent: false,
            matchBrackets: true,
            scrollbarStyle: "overlay",
            readOnly: "nocursor",
        });
        input_box.setSize("auto", "auto");
        input_box.setValue("");
    }
})(jQuery);
