(function ($) {
    var pageNum = 0;
    var theorem = {};
    var variables = [];
    var assumes = [];
    var conclusion = undefined;
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

        // $('#theorem-select').on('change', function (e) {
        //     if (undefined !== theorem[this.value])
        //         document.getElementById('type-label').innerHTML = theorem[this.value] + ': ';
        //     else
        //         document.getElementById('type-label').innerHTML = 'Var: ';
        // });

        $('#add-cell').on('click', function () {
            pageNum++;
            $('#codeTabContent').append(
                $('<div class="code-cell" id="code' + pageNum + '-pan">' +
                    '<label for="code' + pageNum + '"></label> ' +
                    '<textarea' + ' id="code' + pageNum + '""></textarea>'));
            init_editor("code" + pageNum);
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

        $('#init-button').on("click", function () {
            let variables_area = document.querySelector('#variables .CodeMirror').CodeMirror;
            let assumes_area = document.querySelector('#assumes .CodeMirror').CodeMirror;
            let conclusions_area = document.querySelector('#conclusions .CodeMirror').CodeMirror;
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
                    'id': document.querySelector('.code-cell.selected textarea').id,
                    'variables': variables,
                    'assumes': assumes,
                    'conclusion': conclusion
                };
                var data = JSON.stringify(event);

                $.ajax({
                    url: "/api/init",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        if (JSON.stringify(result) !== '{}') {
                            var editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
                            editor.setValue(result['result'])
                        }
                    }
                });
                variables = [];
                assumes = [];
                conclusion = undefined;
            });
        });

        $('#add-cell').click();

        $(function () {
            init_input_box('variables');
            init_input_box('assumes');
            init_input_box('conclusions');
        });
        document.getElementById('open-file').addEventListener('change', function (e) {
            e = e || window.event;

            let files = this.files;
            let editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
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
        document.getElementById("run-button").addEventListener('click', send_input);

        function init_editor(editor_id = "code1") {
            let editor = CodeMirror.fromTextArea(document.getElementById(editor_id), {
                mode: "text/x-python",
                lineNumbers: true,
                theme: "",
                lineWrapping: true,
                foldGutter: true,
                smartIndent: false,
                matchBrackets: true,
                scrollbarStyle: "overlay",
                extraKeys: {
                    "Shift-Ctrl-Enter": function () {
                    }
                }
            });
            editor.setSize("auto", "auto");
            editor.setValue("");
            editor.on("keyHandled", function (cm, name, event) {
                if (name === "Shift-Ctrl-Enter") {
                    send_input()
                }
            });
            editor.on("keydown", function (cm, event) {
                if (event.code === 'Enter') {
                    let line_no = cm.getCursor().line;
                    let line = cm.getLine(line_no);
                    if (line.indexOf('|-') === -1) {

                    }
                }
            });
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
                var line_number = cm.getCursor().line;
                var line = cm.getLine(line_number);
                if (line !== '' && line.indexOf('by') !== -1)
                    proof_line_cov(cm);
            });
            editor.on("change", function (cm, changed) {
                $(document).ready(function () {
                    }
                )
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

        function send_input() {
            $(document).ready(function () {
                    var input = {};
                    var counter = 1;
                    var reg_blank = /^\s*$/g;
                    var editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
                    editor.eachLine(line => {
                        if (!reg_blank.test(line.text))
                            input[counter++] = line.text;
                    });
                    var data = JSON.stringify(input);

                    $.ajax({
                        url: "/api/check-proof",
                        type: "POST",
                        data: data,
                        success: function (result) {
                            $('.code-cell.selected').append(
                                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                                    '<pre></pre></div></div>')
                            );
                            let value = "";
                            for (var i in result) {
                                value += result[i] + '\n';
                            }
                            document.querySelector('.code-cell.selected .output pre').innerHTML = value;
                        }
                    })
                }
            )
        }

        function proof_line_cov(cm) {
            let line_no = cm.getCursor().line;
            let old_string = cm.getLine(line_no);
            let new_string = old_string.split('by ')[0].split(': ')[0] + ': ' + old_string.split('by ')[1];
            replace_line(cm, new_string)
        }

        function replace_line(cm, new_string) {
            let line_no = cm.getCursor().line;
            cm.setCursor(line_no, 0);
            let pre = cm.getCursor();
            cm.setCursor(line_no, Number.MAX_SAFE_INTEGER);
            let post = cm.getCursor();
            cm.replaceRange(new_string, pre, post);
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
                    'id': document.querySelector('.code-cell.selected textarea').id,
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
                            conclusions_area.setValue(result['conclunsion']);
                        }
                    }
                });
                variables = [];
                assumes = [];
                conclusion = undefined;
            });
        }

        function check_type(line) {
            $(document).ready(function () {
                    var input = {'line': line};
                    var data = JSON.stringify(input);

                    $.ajax({
                        url: "/api/check-type",
                        type: "POST",
                        data: data,
                        success: function (result) {
                            $('#theorem-select').selectpicker('val', result['theorem']);
                            if (undefined !== theorem[result['theorem']])
                                document.getElementById('type-label').innerHTML = theorem[result['theorem']] + ': ';
                            else
                                document.getElementById('type-label').innerHTML = 'Var: ';
                        }
                    })
                }
            )
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
    })
})(jQuery);