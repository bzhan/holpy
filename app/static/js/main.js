(function ($) {
    var instructions = [];
    var page_num = 0;
    var index = 0;
    var result_list = [];
    var is_mousedown = false;
    var is_ctrl_click = false;
    var click_count = 0;
    var proof_id = 0;
    var origin_result = [];

    $(document).ready(function () {
        document.getElementById('left').style.height = (window.innerHeight - 40) + 'px';
    });

    $(function () {
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
                    '<textarea id="code' + page_num + '"></textarea>' + '<button id="' + proof_id +'" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:100px;" name="save"><b>SAVE</b></button>'
                    +'<button id="' + proof_id +'" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:100px;" name="reset"><b>RESET</b></button>'));
            init_editor("code" + page_num);
            // Add location for displaying results
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div></div>'));
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<a href="#" id="link-backward" style="float:left;"><</a>' +
                    '<pre id="instruction-number", style="float:left;"> </pre>' +
                    '<a href="#" id="link-forward" style="float:left;">></a>' +
                    '<pre id="instruction" style="float:left;"> </pre></div></div>'));

            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active')
            });
        });

        $('#right').on('click', '#link-backward', function () {
            if (index > 0) {
                index--;
                var instr_output = get_selected_instruction();
                instr_output.innerHTML = instructions[index];
                var instr_no_output = get_selected_instruction_number();
                instr_no_output.innerHTML = (index+1) + '/' + instructions.length;
            }
        });

        $('#right').on('click', '#link-forward', function () {
            if (index < instructions.length - 1) {
                index++;
                var instr_output = get_selected_instruction();
                instr_output.innerHTML = instructions[index];
                var instr_no_output = get_selected_instruction_number();
                instr_no_output.innerHTML = (index+1) + '/' + instructions.length;
            }
        });

        //click save button to save file and update the thm status;
        $('div.rtop').on('click', 'button[name="save"]', function() {
            var editor_id = get_selected_id();
            var id = Number($(this).attr('id'))-1;
            var proof = cells[editor_id]['proof'];
            result_list[id]['proof'] = proof;
            result_list[id]['status'] = 'yellow';
            var str = '';
            if (cells[editor_id]['num_gaps'] === 0) {
                 result_list[id]['status'] = 'green';
            }
            $.each(result_list[id]['prop'], function(i, val) {
                 str = str +'<tt class="'+rp(val[1])+'">'+val[0]+'</tt>';
                        });
            $('div#left_json p:eq(' + id + ')').parent().replaceWith($('<div><div style="float:left;width: 12px; height: 12px; background: '
            + result_list[id]['status'] + ';">&nbsp;</div>'+'<p>'+'<font color="#006000"><b>theorem</b></font> '+ result_list[id]['name'] + ':&nbsp;<a href="#" ' + 'id="'
            +(id+1)+ '">proof</a>'+'</br>&nbsp;&nbsp;&nbsp;'+str+'</p></div>'))
        });

        //click save-file button to save the info into the json-file;
        function save_json_file() {
            var editor_id = get_selected_id();
            var proof = cells[editor_id]['proof'];
            var id = $('div#'+editor_id+'-pan button[name="save"]').attr('id')-1;
            var output_proof = [];
            $.each(proof, function (i) {
                output_proof.push({});
                $.extend(output_proof[i], proof[i]);  // perform copy
                output_proof[i]['th'] = output_proof[i]['th_raw'];
                output_proof[i]['th_raw'] = undefined;
            })
            var data = {
                'name': name,
                'proof': output_proof,
                'id': id,
                'num_gaps': cells[editor_id]['num_gaps']
            }
            if (proof !== '' && id !== -1) {
                save_info(JSON.stringify(data));
            }
        }

        //click reset button to reset the thm to the origin status;
        $('div.rtop').on('click', 'button[name=reset]', function() {
            var id = Number($(this).attr('id'))-1;
                theorem_proof(result_list[id]);
        })

        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            $(this).tab('show');
        });

        $('#codeTab').on('shown.bs.tab', 'a', function (event) {
            var editor = document.querySelector('.code-cell.active textarea + .CodeMirror').CodeMirror;
            var rtop = document.querySelector('.rtop');
            revert_status(editor);
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

        //click proof then send it to the init; including the save-json-file;
        $('#left_json').on('click', 'a', function() {
            proof_id = $(this).attr('id');
             $('a#save-file').click(save_json_file);
            if (result_list[proof_id-1]['proof']) {
                $('#add-cell').click();
                setTimeout(function() {
//                    alert(result_list[proof_id-1]['instructions']);
                    init_saved_proof(result_list[proof_id-1]);
                }, 500);
            }
            else {
                $('#add-cell').click();
                setTimeout(function() {
                    theorem_proof(result_list[proof_id-1]);
                }, 500);
            }

        });

        $('#file-path').on('click', '#root-a', function () {
            $('#left_json').empty();
            if ($('#file-path a:last').text() !== 'root/') {
                $('#file-path a:last').remove();
            };
        });

        $('#root-file').on('click', 'a', function() {
            num = 0;
            $('#left_json').empty();
            $('#add-info').click(add_info);
            name = $(this).text();
            name = $.trim(name);
            if ($('#file-path').html() === '') {
                $('#file-path').append($('<a href="#" id="root-a"><font color="red"><b>root/</b></font></a><a href="#"><font color="red"><b> '+name+'</b></font></a>'));
            } else if ($('#file-path a:last').text() === 'root/') {
                $('#root-a').after($('<a href="#"><font color="red"><b> '+name+'</b></font></a>'));
            } else if ($('#file-path a:last').text() !== name) {
                $('#file-path a:last').remove();
                $('#root-a').after($('<a href="#"><font color="red"><b> '+ name + '</b></font></a>'));
            };
            data = JSON.stringify(name);
            ajax_res(data);
        });

        $('#json-button').on('click', function() {
            num = 0;
            $('#left_json').empty();
            name = prompt('please enter the file name');
            var data = JSON.stringify(name);
            $('#add-info').click(add_info);
            ajax_res(data);
        });

        // On loading page, retrieve list of theories from root file.
        num_root = 0;
        $.ajax({
            url: "/api/root_file",
            success: function(r) {
                $.each(r['theories'], function(i, val) {
                    num_root++;
                    $('#root-file').append($('<a href="#"  ' + 'id="'+ num_root + '"><font color="#006000"><b>'+ val +'</b></font></a></br>'));
                });
            }
        });
    });

    function rp(x) {
        if (x === 0)
            return 'normal';
        if (x === 1)
            return 'bound';
        if (x === 2)
            return 'var';
    }

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

    function theorem_proof(r_data) {
        instructions = r_data['instructions'];
        var event = {
            'id': get_selected_id(),
            'vars': r_data['vars'],
            'prop': r_data['prop_raw'],
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
    }

    function init_saved_proof(r_data) {
        instructions = r_data['instructions'];
        var event = {
            'id': get_selected_id(),
            'vars': r_data['vars'],
            'proof': r_data['proof'],
        };
        var data = JSON.stringify(event);
        display_running();
        $.ajax({
            url: "/api/init-saved-proof",
            type: 'POST',
            data: data,
            success: function (result) {
                display_checked_proof(result);
                get_selected_editor().focus();
                display_instuctions(instructions);
            }
        })
    }

    function save_info(data_save) {
        $.ajax({
            url: "/api/save_proof",
            type: "PUT",
            data: data_save,
            cache: false,
            success: function() {
                alert('save success');
            }
        })
    }

    function add_info() {
        var data = [];
        if ($('#constant, #type').val() !== '') {
            var constant = {};
            var cons = $('#constant').val();
            var type = $('#type').val();
            constant['ty'] = 'def.ax';
            constant['name'] = cons;
            constant['T'] = type;
            data.push(constant);
            $('#constant,#type').val('');
        }

        if ($('#thm, #term, #vars').val() !== '') {
            var theorem = {};
            var vars = {};
            var theo = $('#thm').val();
            var term = $('#term').val();
            var vars_str = $('#vars').val();
            var vars_list = vars_str.split(' ');
            for (var i in vars_list) {
                var v_list = vars_list[i].split(':');
                vars[v_list[0]] = v_list[1];
            }
            theorem['ty'] = 'thm';
            theorem['name'] = theo;
            theorem['vars'] = vars;
            theorem['prop'] = term;
            data.push(theorem);
            $('#thm,#term,#vars').val('');
        }
        var event = {"data": data,
                     "name": name};

        data_ajax = JSON.stringify(event);
        $.ajax({
            url: "/api/json",
            type: "POST",
            data: data_ajax,
            cache: false,
            success: function (result) {
                result_list = result_list.concat(result['data']);
                for (var d in result['data']) {
                    num++;
                    var name = result['data'][d]['name'];
                    var obj = result['data'][d]['prop'];
                    var ty = result['data'][d]['ty'];
                    var str = '';
                    if (ty === 'def.ax') {
                        $('#left_json').append($('<p><font color="#006000"><b>constant</b></font> ' + name + ' :: ' + obj + '</p>'));
                    }

                    if (ty === 'thm'){
                        $.each(obj, function(i, val) {
                            str = str +'<tt class="'+rp(val[1])+'">'+val[0]+'</tt>';
                        });
                        $('#left_json').append($('<div><div style="float:left;width: 12px; height: 12px; background: '+ result['data'][d]['status'] + ';">&nbsp;</div>'+'<p>'+'<font color="#006000"><b>theorem</b></font> '+ name + ':&nbsp;<a href="#" ' + 'id="'+ num+ '">proof</a>'+'</br>&nbsp;&nbsp;&nbsp;'+str+'</p></div>'));
                    }
                }
            }
        });
    }

    function ajax_res(data) {
//        num = 0;
        $.ajax({
            url: "/api/json",
            type: "POST",
            data: data,
            success: function (result) {
                result_list = result_list.concat(result['data']);
//                $('#left_json').empty();
                for (var d in result['data']) {
                    num++;
                    var name = result['data'][d]['name'];
                    var obj = result['data'][d]['prop'];
                    var ty = result['data'][d]['ty'];
                    var str = '';
                    if (ty === 'def.ax') {
                        $('#left_json').append($('<p><font color="#006000"><b>constant</b></font> ' + name + ' :: ' + obj +'</p>'));
                    }

                    if (ty === 'thm') {
                        $.each(obj, function(i, val) {
                            str = str +'<tt class="'+rp(val[1])+'">'+val[0]+'</tt>';
                        });
                        $('#left_json').append($('<div><div style="float:left;width: 12px; height: 12px; background: '+ result['data'][d]['status'] + ';">&nbsp;</div>'+'<p>'+'<font color="#006000"><b>theorem</b></font> '+ name + ':&nbsp;<a href="#" ' + 'id="'+ num+ '">proof</a>'+'</br>&nbsp;&nbsp;&nbsp;'+str+'</p></div>'));
                    }

                    if (ty === 'type.ind'){
                        var constrs = result['data'][d]['constrs'];
                        str = '</br>' + constrs[0]['name'] + '</br>' + constrs[1]['name'];
                        for (var i in constrs[1]['args']) {
                            str += ' (' + constrs[1]['args'][i] + ' :: '+ obj[i] + ')';
                        }
                        $('#left_json').append($('<p><font color="#006000"><b>datatype</b></font> ' + constrs[0]['type'] + ' =' + str + '</p>'));
                    }

                    if (ty === 'def.ind') {
                        $('#left_json').append($('<p id="fun'+j+'"><font color="#006000"><b>fun</b></font> ' + name + ' :: ' + result['data'][d]['type']
                            + ' where'+'</p>'));
                        for (var j in obj) {
                            str = '';
                            $.each(obj[j], function(i, val) {
                                str = str + '<tt class="'+ rp(val[1]) + '">' +val[0] +'</tt>';
                            });
                            $('#left_json p:last').append($('<p>'+ str+'</p>'));
                        }
                    }
                }
            }

        });

    }

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

            if (event.code === 'Enter') {
                event.preventDefault();
                if (edit_line_number !== -1) {
                    set_line(cm);
                } else {
                    add_line_after(cm);
                }
            } else if (event.code === 'Tab') {
                event.preventDefault();
                unicode_replace(cm);
            } else if (event.code === 'Backspace') {
                if (line.endsWith(": ")) {
                    event.preventDefault();
                    remove_line(cm);
                }
            } else if (event.code === 'Escape') {
                event.preventDefault();
                if (edit_line_number !== -1) {
                    cm.getAllMarks().forEach(e => {
                        if (e.readOnly !== undefined) {
                            if (e.readOnly) {
                                e.clear();
                            }
                        }
                    });
                    var id = get_selected_id();
                    display_line(id, edit_line_number);
                    readonly_lines.push(edit_line_number);
                    readonly_lines.sort();
                    edit_line_number = -1;
                }
            }
        });

        editor.on("focus", function (cm, event) {
            $('#codeTabContent .code-cell').each(function () {
                $(this).removeClass('selected');
            });
            $(cm.getTextArea().parentNode).addClass('selected');
        });

        editor.on("cursorActivity", function (cm) {
            if (is_mousedown) {
                mark_text(cm);
                is_mousedown = false;
                is_ctrl_click = false;
            }
        });

        editor.on('beforeChange', function (cm, change) {
            if (!edit_flag && readonly_lines.indexOf(change.from.line) !== -1) {
                change.cancel();
            }
        });

        editor.on('mousedown', function (cm, event) {
            is_mousedown = true;
            if (event.ctrlKey)
                is_ctrl_click = true;
            click_count++;
            if (click_count === 1) {
                timer = setTimeout(function () {
                    if (click_count > 1) {
                        clearTimeout(timer);
                        set_read_only(cm);
                    }
                    click_count = 0;
                }, 300)
            }
        });
    }

    function set_read_only(cm) {
        cm.setCursor(cm.getCursor().line, Number.MAX_SAFE_INTEGER);
        var line_num = cm.getCursor().line;
        var ch = cm.getCursor().ch;
        var line = cm.getLineHandle(line_num).text;
        if (line.indexOf('sorry') !== -1) {
            cm.getAllMarks().forEach(e => {
                if (e.readOnly !== undefined)
                    if (e.readOnly)
                        e.clear();
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            readonly_lines.splice(line_num, 1);
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch - 5}, {readOnly: true});
            cm.addSelection({line: line_num, ch: ch - 5}, {line: line_num, ch: ch});
            edit_line_number = line_num;
        } else if (line.split(': ')[1].trim() === '') {
            cm.getAllMarks().forEach(e => {
                if (e.readOnly !== undefined)
                    if (e.readOnly)
                        e.clear();
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            readonly_lines.splice(line_num, 1);
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {readOnly: true});
            edit_line_number = line_num;
        }
    }

    function mark_text(cm) {
        var origin_pos = cm.getCursor();
        cm.setCursor(cm.getCursor().line, Number.MAX_SAFE_INTEGER);
        var line_num = cm.getCursor().line;
        var ch = cm.getCursor().ch;
        var line = cm.getLineHandle(line_num).text;

        if (is_ctrl_click) {
            var flag = false;
            if (click_line_number !== -1 && line_num < click_line_number)
                flag = true;
            cm.getAllMarks().forEach(e => {
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            if (flag)
                cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {css: 'background: yellow'});
            if (click_line_number !== -1) {
                var click_line = cm.getLineHandle(click_line_number).text;
                var len = click_line.length;
                cm.markText({line: click_line_number, ch: len - 5}, {line: click_line_number, ch: len}, {
                    css: 'background: red'
                })
            }
            ctrl_click_line_number = line_num;
            is_ctrl_click = false;
        } else if (line.indexOf('sorry') !== -1) {
            cm.getAllMarks().forEach(e => {
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            if (ctrl_click_line_number !== -1) {
                var ctrl_click_line = cm.getLineHandle(ctrl_click_line_number).text;
                var len = ctrl_click_line.length;
                cm.markText({line: ctrl_click_line_number, ch: 0}, {line: ctrl_click_line_number, ch: len}, {
                    css: 'background: yellow'
                });
            }
            cm.markText({line: line_num, ch: ch - 5}, {line: line_num, ch: ch}, {
                css: "background: red"
            });
            click_line_number = line_num;
        } else {
            cm.getAllMarks().forEach(e => {
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            click_line_number = -1;
            ctrl_click_line_number = -1;
        }
        cm.setCursor(origin_pos);
    }

    function revert_status(cm) {
        is_mousedown = false;
        is_ctrl_click = false;
        click_count = 0;
        edit_flag = false;
        readonly_lines.length = 0;
        click_line_number = -1;
        ctrl_click_line_number = -1;
        edit_line_number = -1;
        for (var i = 0; i < cm.lineCount(); i++)
            readonly_lines.push(i);
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
})
(jQuery);
