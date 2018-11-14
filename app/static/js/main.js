(function ($) {
    var pageNum = 0;
    var theorem = {};
    var lineNum = -1;
    $(document).ready(function () {
        $('#theorem-select').ready(function () {
            $(document).ready(function () {
                var event = { 'event': 'init_theorem' };
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

        $('#theorem-select').on('change', function (e) {
            if (undefined !== theorem[this.value])
                document.getElementById('type-label').innerHTML = theorem[this.value] + ': ';
            else
                document.getElementById('type-label').innerHTML = 'Var: ';
        });

        $('#add-cell').click(function () {
            pageNum++;
            $('#codeTabContent').append(
                $('<div class="code-cell" id="code' + pageNum + '-pan">' +
                    '<label for="code' + pageNum + '"></label> ' +
                    '<textarea' + ' id="code' + pageNum + '""></textarea>'));
            init_editor("code" + pageNum);
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

        $('#insert-button').on("click", function () {
            let editor = document.querySelector('.code-cell-selected textarea + .CodeMirror') === null ? document.querySelector('.code-cell textarea + .CodeMirror') : document.querySelector('.code-cell-selected textarea + .CodeMirror');
            editor = editor.CodeMirror
            let input_box = document.querySelector('#input-box .CodeMirror').CodeMirror;
            var reg_blank = /^\s*$/g;
            var lines = editor.getValue();
            input_box.eachLine(line => {
                if (!reg_blank.test(line.text)) {
                    if (lines === "")
                        lines += line.text;
                    else
                        lines += '\n' + line.text;
                }
            });
            editor.setValue(lines);
            input_box.setValue('');

        });

        $('#add-cell').click();

        $(function () {
            let input_box = CodeMirror(document.getElementById('input-box'), {
                mode: "text/groovy",
                mode: "text/x-python",
                lineNumbers: true,
                lineWrapping: false,
                foldGutter: true,
                gutters: ["CodeMirror-linenumbers", "CodeMirror-foldgutter"],
                theme: "",
                scrollbarStyle: "overlay",
            });
            input_box.setSize("auto", "auto");
            input_box.setValue("");
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
                mode: "text/groovy",
                mode: "text/x-java",
                mode: "text/x-python",
                lineNumbers: true,
                theme: "",
                lineWrapping: false,
                foldGutter: true,
                gutters: ["CodeMirror-linenumbers", "CodeMirror-foldgutter"],
                matchBrackets: true,
                scrollbarStyle: "overlay",
                extraKeys: {
                    "Shift-Ctrl-Enter": function () {
                    }
                }
            });
            editor.setSize("auto", "auto");
            editor.setValue("");
            editor.on("keyHandled", function (cm, name) {
                if (name === "Shift-Ctrl-Enter") {
                    send_input()
                }
            });
            editor.on("cursorActivity", function (doc) {
                set_theorem_select(doc);
                var line_number = doc.getCursor().line;
                var line = doc.getLine(line_number);
                let input_box = document.querySelector('#input-box .CodeMirror').CodeMirror;
                input_box.setValue(line);
                check_type(line);
            });
            editor.on("focus", function (cm, event) {
                $('#codeTabContent .code-cell').each(function () {
                    $(this).removeClass('selected');
                });
                $(cm.getTextArea().parentNode).addClass('selected');
            });
            editor.on("change", function (cm, changed) {
                $(document).ready(function () {
                    // console.log(changed);
                    // var input = {"line": line.text};
                    // var data = JSON.stringify(input);

                    // $.ajax({
                    //     url: "/api/check-proof",
                    //     type: "POST",
                    //     data: data,
                    //     success: function (result) {
                    //         let output = document.querySelector("#output-iframe + .CodeMirror").CodeMirror;
                    //         for (var i in result) {
                    //             if (output.getValue() === "")
                    //                 output.setValue(output.getValue() + result[i]);
                    //             else
                    //                 output.setValue(output.getValue() + "\n" + result[i]);
                    //         }
                    //     }
                    // })
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

        function check_type(line) {
            $(document).ready(function () {
                var input = { 'line': line }
                var data = JSON.stringify(input);

                $.ajax({
                    url: "/api/check-type",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        $('#theorem-select').selectpicker('val', result['theorem']);
                        // if (undefined !== theorem[result['theorem']])
                        //     document.getElementById('type-label').innerHTML = theorem[result['theorem']] + ': ';
                        // else
                        //     document.getElementById('type-label').innerHTML = 'Var: ';
                    }
                })
            }
            )
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

        // function remove_page(first) {
        //     if (first)
        //         pageNum = 0;
        //     else
        //         pageNum = 1;
        //     $('#codeTab > li').each(function () {
        //         var pageId = $(this).children('a').attr('href');
        //         if (pageId === "#code1-pan") {
        //             return true;
        //         }
        //         pageNum++;
        //         $(this).children('a').html('Page ' + pageNum +
        //             '<button id="close_tab" type="button" ' +
        //             'title="Remove this page">×</button>');
        //     });
        // }


    })
})(jQuery);