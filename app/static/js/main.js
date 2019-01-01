(function ($) {
    var instructions = [];
    var page_num = 0;
    var index = 0;
    var theorem = {};
    var is_mousedown = false;
    var is_crlt_click = false;

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
            page_num++;
            // Add CodeMirror textarea
            var id = 'code' + page_num + '-pan';
            $('#codeTab').append(
                $('<li class="nav-item"><a  class="nav-link" ' +
                    'data-toggle="tab"' +
                    'href="#code' + page_num + '-pan">' +
                    'Page ' + page_num +
                    '<button id="close_tab" type="button" ' +
                    'title="Remove this page">×</button>' +
                    '</a></li>'));
            let class_name = 'tab-pane fade active newCodeMirror code-cell';
            if (page_num === 1)
                class_name = 'tab-pane fade in active code-cell';
            $('#codeTabContent').append(
                $('<div class="' + class_name + '" id="code' + page_num + '-pan">' +
                    '<label for="code' + page_num + '"></label> ' +
                    '<textarea' + ' id="code' + page_num + '""></textarea>'));
            init_editor("code" + page_num);
            // Add location for displaying results
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div></div>'));
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<a href="#" id="link-left" style="float:left;"><</a><pre id="instruction" style="float:left;"> </pre>'
                    + '<a href="#" id="link-right" style="float:left;">></a></div></div>'));

            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active')
            });
        });

        $('#right').on('click', '#link-left', function () {
            if (index < instructions.length - 1) {
                index++;
                var status_output = get_selected_instruction();
                status_output.innerHTML = instructions[index];
            }
        });

        $('#right').on('click', '#link-right', function () {
            if (index > 0) {
                index--;
                var status_output = get_selected_instruction();
                status_output.innerHTML = instructions[index];
            }
        });

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
                var id = get_selected_id();
                $('#codeTab a:first').tab('show');
                delete cells.id;
            }
        });

        function remove_page(first) {
            if (first)
                page_num = 0;
            else
                page_num = 1;
            $('#codeTab > li').each(function () {
                var pageId = $(this).children('a').attr('href');
                if (pageId === "#code1-pan") {
                    return true;
                }
                page_num++;
                $(this).children('a').html('Page ' + page_num +
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

                                    if (ty === 'def.ax') {
                                        $('#left').append($('<p><font color="#006000"><b>constant</b></font> ' + name + ' :: ' + obj + '</p>'))
                                    }

                                    if (ty === 'thm') {
                                        $.each(obj, function (i, val) {
                                            str = str + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                                        })
                                        $('#left').append($('<p><font color="#006000"><b>theorem</b></font> ' + name + ':&nbsp;<a href="#">proof</a></br>&nbsp;&nbsp;&nbsp;' + str + '</p>'));
                                    }

                                    if (ty === 'type.ind') {
                                        var constrs = result['data'][d]['constrs'];
                                        str = '</br>' + constrs[0]['name'] + '</br>' + constrs[1]['name']
                                        for (var i in constrs[1]['args']) {
                                            str += ' (' + constrs[1]['args'][i] + ' :: ' + obj[i] + ')';
                                        }
                                        $('#left').append($('<p><font color="#006000"><b>datatype</b></font> ' + constrs[0]['type'] + ' =' + str + '</p>'));
                                    }

                                    if (ty === 'def.ind') {
                                        $('#left').append($('<p id="fun' + j + '"><font color="#006000"><b>fun</b></font> ' + name + ' :: ' + result['data'][d]['type']
                                            + ' where' + '</p>'))
                                        for (var j in obj) {
                                            str = ''
                                            $.each(obj[j], function (i, val) {
                                                str = str + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                                            })
                                            $('#left p').last().append($('<p>' + str + '</p>'));
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

        $('#left').on('click', 'a', function () {
            $('#add-cell').click();
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

        editor.on("cursorActivity", function (cm) {
            if (is_mousedown) {
                mark_text(cm);
                is_mousedown = false;
                is_crlt_click = false;
            }
        });

        editor.on('beforeChange', function (cm, change) {
            console.log(change);
            if (edit_flag) {
                edit_flag = false;
                return;
            } else if (readonly_lines.indexOf(change.from.line) !== -1) {
                change.cancel();
            }
        });

        editor.on('mousedown', function (cm, event) {
            is_mousedown = true;
            if (event.ctrlKey)
                is_crlt_click = true;
        });

        editor.on('dblclick', function (cm, event) {
            console.log(cm);
            console.log(event);
            set_read_only(cm);
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

    function set_read_only(cm) {
        cm.setCursor(cm.getCursor().line, Number.MAX_SAFE_INTEGER);
        var line_num = cm.getCursor().line;
        var ch = cm.getCursor().ch;
        readonly_lines.splice(line_num, 1);
        cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch - 5}, {readOnly: true});
    }

    function mark_text(cm) {
        var line_num = cm.getCursor().line;
        var ch = cm.getCursor().ch;
        var line = cm.getLineHandle(line_num).text;
        if (is_crlt_click) {
            var flag = false;
            if(click_line_number !== -1 && line_num < click_line_number)
                flag = true;
            cm.getAllMarks().forEach(e => {
                if (e.css.indexOf('background') !== -1)
                    e.clear();
            });
            if (flag)
                cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {css: 'background: yellow'})
            ctrl_click_line_number = line_num;
            is_crlt_click = false;
        }
        else if (line.indexOf('sorry') !== -1) {
            cm.getAllMarks().forEach(e => {
                if (e.css.indexOf('color') !== -1)
                    e.clear();
            });
            cm.markText({line: line_num, ch: ch - 5}, {line: line_num, ch: ch}, {
                css: "color: red"
            });
            click_line_number = line_num;
        }else {
            cm.getAllMarks().forEach(e => {
                if(e.css.indexOf('color') !== -1 || e.css.indexOf('background') !== -1)
                    e.clear();
            });
            click_line_number = -1;
            ctrl_click_line_number = -1;
        }
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
