(function ($) {
    var pageNum = 0;
    var theorem = {};
    var replace_obj = {
        "\\lambda" : "λ",
        "%" : "λ",
        "\\forall" : "∀",
        "\\exists" : "∃",
        "\\and" : "∧",
        "&" : "∧",
        "\\or" : "∨",
        "|" : "∨",
        "-->" : "⟶",
        "~" : "¬",
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

    function display_running() {
        var status_output = get_selected_output();
        status_output.innerHTML = "Running";
    }

    function display_checked_proof(result) {
        var editor = get_selected_editor();
        var status_output = get_selected_output();

        if ("failed" in result) {
            status_output.innerHTML = result["failed"] + ": " + result["message"]
        }
        else {
            editor.setValue(result["proof"]);
            var num_gaps = result["report"]["num_gaps"];
            if (num_gaps > 0) {
                status_output.innerHTML = "OK. " + num_gaps + " gap(s) remaining."
            }
            else {
                status_output.innerHTML = "OK. Proof complete!"
            }
        }
    }

    $(document).ready(function () {
        document.querySelector('.pans').style.height = '665px';
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
            $('#codeTabContent').append(
                $('<div class="code-cell" id=' + id + '>' +
                    '<label for="code' + pageNum + '"></label> ' +
                    '<textarea' + ' id="code' + pageNum + '""></textarea></div>'));
            init_editor("code" + pageNum);
            // Add location for displaying results
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div></div>'));
        });

        $('#delete-cell').on('click', function () {
            $('.code-cell.selected').remove();
        });

        $('#clear').on("click", function () {
            clear_output();
        });

        $('#check-box').on("click", function () {
            switch_check_box();
        });


        $('#check-box-inner').on("click", function () {
            switch_check_box();
        });

        $('#introduction').on("click", function () {
            introduction(get_selected_editor());
        });

        $('#addlinebelow').on("click", function () {
            add_line_after(get_selected_editor());
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
            for (; f = files[i]; i++) {
                let reader = new FileReader();
                reader.onload = (function () {
                    var json_data = JSON.parse(this.result);
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
                        }
                    });
                });
                reader.readAsText(f);
            }
        });
        document.getElementById("run-button").addEventListener('click', send_input);

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
                    "Ctrl-B": apply_backward_step
                }
            });
            editor.setSize("auto", "auto");
            editor.setValue("");
            editor.on("keydown", function (cm, event) {
                let line_no = cm.getCursor().line;
                let line = cm.getLine(line_no);

                console.log(event.code);
                if (event.ctrlKey && event.code === 'Enter') {
                    event.preventDefault();
                    send_input();
                }
                else if (event.code === 'Enter') {
                    event.preventDefault();
                    add_line_after(cm);
                }
                else if (event.code === 'Tab') {
                    event.preventDefault();
                    unicode_replace(cm);
                }
                else if (event.code === 'Backspace') {
                    if (line.endsWith(": ")) {
                        event.preventDefault();
                        remove_line(cm);
                    }
                }
                })
            };
            editor.on("focus", function (cm, event) {
                $('#codeTabContent .code-cell').each(function () {
                    $(this).removeClass('selected');
                });
                $(cm.getTextArea().parentNode).addClass('selected');
                document.querySelector('#variables .CodeMirror').CodeMirror.setOption('readOnly', false);
                document.querySelector('#assumes .CodeMirror').CodeMirror.setOption('readOnly', false);
                document.querySelector('#conclusions .CodeMirror').CodeMirror.setOption('readOnly', false);
                set_theorem_select(cm);
                get_cell_state();
            });
//            editor.on("change", function (cm, changed) {
//                $(document).ready(function () {
//                    }
//                )
//            })
        })

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
                    var line_number = editor.getCursor().line;
                    var input = {
                        "id": get_selected_id(),
                        "proof" : editor.getValue()
                    };
                    var data = JSON.stringify(input);
                    display_running();

                    $.ajax({
                        url: "/api/check-proof",
                        type: "POST",
                        data: data,
                        success: function (result) {
                            display_checked_proof(result);
                            editor.setCursor(line_number, Number.MAX_SAFE_INTEGER);
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
                onOpen: function (){
                    init_select_abs()
                },
                showCancelButton: true,
                confirmButtonText: 'confirm',
                showLoaderOnConfirm: true,
                preConfirm: () => {
                    var data = {
                        'id': get_selected_id(),
                        "line": line,
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

         function unicode_replace(cm) {
            $(document).ready(function () {
                var cur_position = cm.getCursor()
                var line_number = cur_position.line
                var line = cm.getLine(line_number)
                var position = cm.getCursor().ch
                var stri = cm.getRange({line:line_number,ch:0},cm.getCursor());
                if (position > 0){
                    for (var key in replace_obj){
                        for (var i=1; i<=stri.length; i++){
                            if (stri.slice(-i) === key){
                                start_position = {line:line_number,ch:position-i};
                                cm.replaceRange(replace_obj[key],start_position,cur_position);
                            }
                        }
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

        function clear_output() {
            let output = document.querySelector("#output-iframe + .CodeMirror").CodeMirror;
            output.setValue("");
        }

        function switch_check_box() {
            if ($('#check-box').hasClass("is-checked")) {
                $('#check-box').removeClass("is-checked");
                $('#auto-run').removeClass("is-checked");
                $('#auto-run').removeAttr("aria-checked", "true");
            }
            else {
                $('#check-box').addClass("is-checked");
                $('#auto-run').addClass("is-checked");
                $('#auto-run').attr("aria-checked", "true");
            }
        }
    })(jQuery);