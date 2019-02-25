(function ($) {
    var instructions = [];
    var page_num = 0;
    var index = 0;
    var theory_name = "";  // Name of the current theory file
    var theory_imports = [];  // List of imports of the current theory file
    var result_list = [];  // Content of the current theory file
    var theory_desc = "";  // Description of the theory
    var is_mousedown = false;
    var is_ctrl_click = false;
    var click_count = 0;
    var proof_id = 0;
    var origin_result = [];
    var edit_mode = false;

    $(document).ready(function () {
        document.getElementById('left').style.height = (window.innerHeight - 40) + 'px';
    });

    $(function () {
        $('#add-cell').on('click', function () {
            page_num++;
            // Add CodeMirror textarea;
            var id = 'code' + page_num + '-pan';
            $('#codeTab').append(
                $('<li class="nav-item" name="code'+ page_num +'"><a class="nav-link" ' +
                    'data-toggle="tab"' +
                    'href="#code' + page_num + '-pan">' +
                    '<span> ' +
                    '</span><button id="close_tab" type="button" ' +
                    'title="Remove this page" name="proof-tab">×</button>' +
                    '</a></li>'));
            let class_name = 'tab-pane fade active newCodeMirror code-cell';
            if (page_num === 1)
                class_name = 'tab-pane fade in active code-cell';
            $('#codeTabContent').append(
                $('<div class="' + class_name + '" id="code' + page_num + '-pan">' +
                    '<label for="code' + page_num + '"></label> ' +
                    '<textarea id="code' + page_num + '"></textarea>' +
                    '<button id="' + proof_id + '" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:100px;" name="save"><b>SAVE</b></button>' +
                    '<button id="' + proof_id + '" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:100px;" name="reset"><b>RESET</b></button></div>'));
            init_editor("code" + page_num);
            // Add location for displaying results;
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div><div class="match-thm""></div></div>'));
            $('#' + id).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<a href="#" id="link-backward" style="float:left;"><</a>' +
                    '<pre id="instruction-number", style="float:left;"> </pre>' +
                    '<a href="#" id="link-forward" style="float:left;">></a>' +
                    '<pre id="instruction" style="float:left;"> </pre></div></div>'));

            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active');
            });
        });

        $('#right').on('click', '.backward-step', function () {
            apply_backward_step(get_selected_editor(), is_others = true);
        });

        $('#right').on('click', '.thm-content pre', function () {
            apply_backward_step(get_selected_editor(), is_others = false, select_thm = $(this).index());
        });

        $('#right').on('click', '#link-backward', function () {
            if (index > 0) {
                index--;
                var instr_output = get_selected_instruction();
                instr_output.innerHTML = instructions[index];
                var instr_no_output = get_selected_instruction_number();
                instr_no_output.innerHTML = (index + 1) + '/' + instructions.length;
            }
        });

        $('#right').on('click', '#link-forward', function () {
            if (index < instructions.length - 1) {
                index++;
                var instr_output = get_selected_instruction();
                instr_output.innerHTML = instructions[index];
                var instr_no_output = get_selected_instruction_number();
                instr_no_output.innerHTML = (index + 1) + '/' + instructions.length;
            }
        });

        // Save a single proof to the webpage (not to the json file);
        $('div.rtop').on('click', 'button[name="save"]', function () {
            editor_id_list = [];
            var editor_id = get_selected_id();
            var id = Number($(this).attr('id')) - 1;
            var proof = cells[editor_id]['proof'];
            var output_proof = [];
            $.each(proof, function (i) {
                output_proof.push({});
                $.extend(output_proof[i], proof[i]);  // perform copy
                output_proof[i]['th'] = output_proof[i]['th_raw'];
                output_proof[i]['th_raw'] = undefined;
                output_proof[i]['args'] = output_proof[i]['args_raw'];
                output_proof[i]['args_raw'] = undefined;
            })
            result_list[id]['proof'] = output_proof;
            result_list[id]['num_gaps'] = cells[editor_id]['num_gaps'];
            display_result_list();
        });

        function result_to_output(data) {
            if (data.ty === 'def.ax') {
                data.type_hl = undefined;
            }
            else if (data.ty === 'thm') {
                data.prop_hl = undefined;
            }
            else if (data.ty === 'type.ind') {
                data.argsT = undefined;
            }
            else if (data.ty === 'def.ind') {
                data.type_hl = undefined;
                for (var i in data.rules) {
                    data.rules[i].prop_hl = undefined;
                }
            }
        }

//      save all of the modified_data to the json-file;
        function save_editor_data() {
            var copy_result_list = result_list;
            $.each(copy_result_list, function (i, v) {
                if (v.ty === 'def.ax') {
                    delete v.type_hl;
                }
                else if (v.ty === 'thm') {
                    delete v.prop_hl;
                }
                else if (v.ty === 'type.ind') {
                    delete v.argsT;
                }
                else if (v.ty === 'def.ind') {
                    delete v.type_hl;
                    for (var i in v.rules) {
                        delete v.rules[i].prop_hl;
                    }
                }
            })
            $.ajax({
                url: '/api/editor_file',
                type: 'PUT',
                data: JSON.stringify({
                    'name' : name,
                    'data' : copy_result_list
                }),
                success: function() {
                    alert('save success');
                }
            })
        }

        // Save all changes on the webpage to the json-file;
        function save_json_file() {
            var output_list = [];
            for (var d in result_list) {
                output_list[d] = {};
                $.extend(output_list[d], result_list[d])  // perform copy
                result_to_output(output_list[d]);
            }
            var data = {
                'name': name,
                'data': {
                    'name': theory_name,
                    'imports': theory_imports,
                    'description': theory_desc,
                    'content': output_list
                }
            }
            $.ajax({
                url: "/api/save_file",
                type: "POST",
                data: JSON.stringify(data),
                success: function () {
                    alert('save success');
                }
            });
        }

        //click reset button to reset the thm to the origin status;
        $('div.rtop').on('click', 'button[name=reset]', function () {
            var id = Number($(this).attr('id')) - 1;
            theorem_proof(result_list[id]);
        })

        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            $(this).tab('show');
        });

        $('#codeTab').on('shown.bs.tab', 'a', function (event) {
            if (document.querySelector('.code-cell.active textarea + .CodeMirror')) {
                var editor = document.querySelector('.code-cell.active textarea + .CodeMirror').CodeMirror;
                var rtop = document.querySelector('.rtop');
                editor.focus();
                editor.setCursor(editor.lineCount(), Number.MAX_SAFE_INTEGER);
                editor.setSize("auto", rtop.clientHeight - 40);
                editor.refresh();
            }
        });

        $('#codeTab').on('click', 'li button[name="proof-tab"]', function () {
            var id = get_selected_id();
            var tabId = $(this).parents('li').children('a').attr('href');
            delete cells[id];
            $(this).parents('li').remove('li');
            $(tabId).remove();
            $('#codeTab a:first').tab('show');
        });

        $('#codeTab').on('click', 'li button[name="edit"]', function() {
            var tabId = $(this).parents('li').children('a').attr('href');
            $(this).parents('li').remove('li');
            $(tabId).remove();
            $('#codeTab a:first').tab('show');
        })

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

        //click proof then send it to the init; including the save-json-file;
        $('#left_json').on('click', 'a[name="proof"]', function () {
            proof_id = $(this).attr('id');
            eidt_mode = false;
            var thm_name = $(this).parent().find('span#thm_name').text();
            if (result_list[proof_id - 1]['proof']) {
                $('#add-cell').click();
                setTimeout(function () {
                    $('#codeTab li[name="'+ get_selected_id() +'"] span').text(thm_name);
                    init_saved_proof(result_list[proof_id - 1]);
                }, 200);
            } else {
                $('#add-cell').click();
//                $('#codeTab li[name="'+get_selected_id()+'"] span').text(thm_name);
                setTimeout(function () {
                    $('#codeTab li[name="'+get_selected_id()+'"] span').text(thm_name);
                    theorem_proof(result_list[proof_id - 1]);
                }, 200);
            }
        });

//      click edit then create a tab page for the editing;
        $('#left_json').on('click', 'a[name="edit"]', function() {
            page_num++;
            edit_mode = true;
            var vars_str = '';
            var a_id = $(this).attr('id').trim();
            var number = Number(a_id.slice(5,))-1;
            for(var key in result_list[number]['vars']) {
                vars_str += key + ':' + result_list[number]['vars'][key] +' ';
            };
            var data_name = $(this).parents('p').find('span[name="name"]').text().trim();
            var data_type = $(this).parents('p').find('span:eq(0)').attr('name').trim();
            var data_content = $(this).parents('p').find('span[name="content"]').text().trim();
            $('#codeTab').append(
                $('<li class="nav-item" name="code'+ page_num +'"><a class="nav-link" ' +
                    'data-toggle="tab"' +
                    'href="#code' + page_num + '-pan">' +
                    '<span id="'+ page_num +'">' + data_name +
                    '</span><button id="close_tab" type="button" ' +
                    'title="Remove this page" name="edit">×</button>' +
                    '</a></li>'));
            var class_name = 'tab-pane fade in active code-cell edit-data';
            if (data_type === 'constant') {
                $('#codeTabContent').append(
                    $('<div style="margin-left:5px;margin-top:20px;" name="'+ a_id +'" class="' + class_name + '" id="code' + page_num + '-pan">' +
                        '<label name="'+ page_num +'" for="code' + page_num + '"></label> ' +
                        '<font color="#006000"><b>constant</b></font>:&nbsp;<input id="data-name'+ page_num +'" style="background:transparent;border:1px;solid #ffffff;width:10%;" value="' + data_name + '">' +
                        '&nbsp;&nbsp;&nbsp;::&nbsp;&nbsp;&nbsp;<input id="data-content'+ page_num +'" style="width:50%;background:transparent;border:1px;solid #ffffff;" value="' + data_content + '">' +
                        '<br><button id="save-edit" name="'+  data_type +'" class="el-button el-button--default el-button--mini" style="margin-top:10px;width:20%;"><b>SAVE</b></button></div>'));
                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'theorem') {
                $('#codeTabContent').append(
                    $('<div style="margin-left:5px;margin-top:20px;" name="'+ a_id +'" class="' + class_name + '" id="code' + page_num + '-pan">' +
                        '<label name="'+ page_num +'" for="code' + page_num + '"></label> ' +
                        '<font color="#006000"><b>theorem</b></font>:&nbsp;<input id="data-name'+ page_num +'" style="margin-top:0px;width:20%;background:transparent;border:1px;solid #ffffff;" value="' + data_name + '">' +
                        '<br><br>vars:&nbsp;&nbsp;&nbsp;&nbsp;<input id="data-vars'+ page_num +'" style="width:30%;background:transparent;border:1px;solid #ffffff;" value="'+ vars_str +'">' +
                        '<br><br>term:&nbsp;&nbsp;&nbsp;<input id="data-content'+ page_num +'" style="width:30%;background:transparent;border:1px;solid #ffffff;" value="'+ data_content +'">'+
                        '<br><button id="save-edit" name="'+  data_type +'" class="el-button el-button--default el-button--mini" style="margin-left:44px;margin-top:5px;width:20%;"><b>SAVE</b></button></div>'));
                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'datatype') {
                var data_content_list = data_content.split(/\s\s/);
                var data_new_content = data_content_list.join('\n');
                $('#codeTab').find('span#'+ page_num).text(data_name.split(/\s/)[1]);
                $('#codeTabContent').append(
                    $('<div style="margin-left:5px;margin-top:20px;" name="'+ a_id +'" class="' + class_name + '" id="code' + page_num + '-pan">' +
                        '<label name="'+ page_num +'" for="code' + page_num + '"><font color="#006000"><b>datatype</b></font>:</label> ' +
                        '<br><input id="data-name'+ page_num +'" style="width:10%;background:transparent;border:1px;solid #ffffff;" value="' + data_name + '">' + '&nbsp;&nbsp;=&nbsp;&nbsp;'+
                        '<br><textarea spellcheck="false" id="data-content'+ page_num +'" style="height:60px;width:30%;background:transparent;border:1px;solid #ffffff;">'+ data_new_content +'</textarea>' +
                        '<br><button id="save-edit" name="'+  data_type +'" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:20%;"><b>SAVE</b></button></div>'));
                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'fun') {
                var data_content_list = data_content.split(/\s\s/);
                var data_new_content = '';
                for (var i in data_content_list) {
                    data_new_content += i+ ': '+ data_content_list[i]+ '\n';
                };
                $('#codeTab').find('span#'+ page_num).text(data_name.split(' :: ')[0]);
                $('#codeTabContent').append(
                    $('<div style="margin-left:5px;margin-top:20px;" name="'+ a_id +'" class="' + class_name + '" id="code' + page_num + '-pan">' +
                        '<label name="'+ page_num +'" for="code' + page_num + '"><font color="#006000"><b>fun</b></font>:</label> ' +
                        '<input id="data-name'+ page_num +'" style="width:30%;background:transparent;border:1px;solid #ffffff;" value="'+ data_name +'">' +
                        '<br><textarea spellcheck="false" id="data-content'+ page_num +'" style="margin-top:5px;height:70px;width:40%;background:transparent;border:1px;solid #ffffff;" name="content">' + data_new_content + '</textarea>' +
                        '&nbsp;&nbsp;for:&nbsp;&nbsp;<textarea spellcheck="false" id="data-vars'+ page_num +'" style="margin-top:5px;height:70px;width:40%;background:transparent;border:1px;solid #ffffff;" placeholder="vars"></textarea>' +
                        '<br><button id="save-edit" name="'+  data_type +'" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:20%;"><b>SAVE</b></button></div>'));
                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
                display_lines_number(data_content_list, page_num, number);
            }
              $('#codeTabContent div#code'+page_num+'-pan button').after(
                $('<div class="output-wrapper" style="margi-top:1px;" id="error'+ page_num +'">' +
                    '<pre></pre></div>'));
        })

//      display lines_number in the textarea;
        function display_lines_number(content_list, page_num, number) {
            var data_vars_list = [];
            var data_vars_str = '';
            $.each(result_list[number]['rules'], function(i, v) {
                var vars_str = '';
                for (let key in v.vars) {
                    vars_str += key+ ':'+ v.vars[key]+ '   ';
                }
//                vars_str += '\n';
                data_vars_list.push(vars_str);
                });
            $.each(data_vars_list, function(i, v) {
                data_vars_str += i+ ': '+ v + '\n';
            })
            $('textarea#data-vars'+ page_num).val(data_vars_str);
        }

//      click save button to save content to the left-json for updating;
        $('#codeTabContent').on('click', 'button#save-edit', function() {
            var a_id = $(this).parent().attr('name').trim();
            var error_id = $(this).next().attr('id').trim();
            var id = $(this).prevAll('label').attr('name').trim();
            var ty = $(this).attr('name').trim();
            var ajax_data = make_data(ty, id);
            var number = Number(a_id.slice(5,))-1;
            var prev_list = result_list.slice(0, number);
            ajax_data['file-name'] = name;
            ajax_data['prev-list'] = prev_list;
            $.ajax({
                url: '/api/save_modify',
                type: 'POST',
                data: JSON.stringify(ajax_data),
                success: function(res) {
                    var result_data = res['data'];
                    var data_name = result_data['name'];
                    var error = res['error']
                    delete result_data['file-name'];
                    delete result_data['prev-list'];
                    if (error && error !== {}) {
                        var error_info = error['detail-content'];
                        $('div#'+error_id).find('pre').text(error_info);
                    }
                    $.each(result_list, function(j,k) {
                        if (k['name'] === data_name) {
                            for (var key in result_data) {
                                result_list[j][key] = result_data[key];
                            }
                        }
                    });
                    display_result_list();
                }
            });
        })

//      make a strict-type data from editing;
        function make_data(ty, id) {
            var data_name = $('input#data-name'+id).val().trim();
            var data_content = $('#data-content'+id).val().trim();
            var ajax_data = {};
            if (ty === 'constant') {
                ajax_data['ty'] = 'def.ax';
                ajax_data['name'] = data_name;
                ajax_data['type'] = data_content;
            }
            if (ty === 'theorem') {
                var vars_str_list = $('input#data-vars'+id).val().split(' ');
                var vars_str = {};
                ajax_data['ty'] = 'thm';
                ajax_data['name'] = data_name;
                ajax_data['prop'] = data_content;
                $.each(vars_str_list, function(i,v) {
                    let v_list = v.split(':');
                    vars_str[v_list[0]] = v_list[1];
                   });
                ajax_data['vars'] = vars_str;
            }
            if (ty === 'datatype') {
                var temp_list = [], temp_constrs = [];
                var temp_content_list = data_content.split(/\n/);
                if (data_name.split(/\s/).length>1) {
                    temp_list.push(data_name.split(/\s/)[0].slice(1,));
                    ajax_data['name'] = data_name.split(/\s/)[1];
                }
                else {
                    ajax_data['name'] = data_name;
                }
                $.each(temp_content_list, function(i,v) {
                    var temp_con_list = v.split(') (');
                    var temp_con_dict = {};
                    var arg_name = '', args = [], type = '';
                    if (temp_con_list[0].indexOf('(')>0) {
                        arg_name = temp_con_list[0].slice(0,temp_con_list[0].indexOf('(')-1);
                        if (temp_con_list.length>1) {
                            temp_con_list[0] = temp_con_list[0].slice(temp_con_list[0].indexOf('(')+1,)
                            temp_con_list[temp_con_list.length-1] = temp_con_list[temp_con_list.length-1].slice(0,-1);
                            $.each(temp_con_list, function(i,v) {
                                args.push(v.split(' :: ')[0]);
                                type += v.split(' :: ')[1] + '⇒';
                                if (v.split(' :: ')[1].indexOf('⇒')>=0) {
                                    type += '(' + v.split(' :: ')[1] + ')' + '⇒'
                                }
                            })
                            type = type + data_name;
                        }
                        else {
                            let vars_ = temp_con_list[0].slice(temp_con_list[0].indexOf('(')+1,-1).split(' :: ')[0];
                            type = temp_con_list[0].slice(temp_con_list[0].indexOf('(')+1,-1).split(' :: ')[1]
                            args.push(vars_);
                            type = type + '=>' + data_name;
                        }
                    }
                    else {
                        arg_name = temp_con_list[0];
                        type = ajax_data['name'];
                    }
                    temp_con_dict['type'] = type;
                    temp_con_dict['args'] = args;
                    temp_con_dict['name'] = arg_name;
                    temp_constrs.push(temp_con_dict);
                })
                ajax_data['ty'] = 'type.ind';
                ajax_data['args'] = temp_list;
                ajax_data['constrs'] = temp_constrs;
            }
            if (ty === 'fun') {
                var rules_list = [];
                var props_list = data_content.split(/\n/);
                var vars_list = $('textarea#data-vars'+id).val().trim().split(/\n/);
                $.each(props_list, function(i,v) {
                    props_list[i] = v.slice(3,);
                    vars_list[i] = vars_list[i].slice(3,);
                })
                $.each(props_list, function(i, v) {
                    var temp_dict = {},temp_vars={};
                    if (v && vars_list[i]) {
                        temp_dict['prop'] = v;
                        $.each(vars_list[i].split(/\s\s/), function(j, k) {
                            temp_vars[k.split(':')[0]] = k.split(':')[1];
                        })
                    }
                    else if (!v) {
                        return true;
                    }
                    temp_dict['vars'] = temp_vars;
                    rules_list.push(temp_dict);
                })
                ajax_data['rules'] = rules_list;
                ajax_data['ty'] = 'def.ind';
                ajax_data['name'] = data_name.split(' :: ')[0];
                ajax_data['type'] = data_name.split(' :: ')[1];
            }

            return ajax_data;
        }

        $('#file-path').on('click', '#root-a', function () {
            $('#left_json').empty();
            if ($('#file-path a:last').text() !== 'root/') {
                $('#file-path a:last').remove();
            }
        });

        $('a#save-file').click(function() {
            if (edit_mode) {
                save_editor_data();
            }
            else {
                save_json_file();
            }
        });

        $('#root-file').on('click', 'a', function () {
            num = 0;
            $('#left_json').empty();
            $('#add-info').click(add_info);
            name = $(this).text();
            name = $.trim(name);
            if ($('#file-path').html() === '') {
                $('#file-path').append($('<a href="#" id="root-a"><font color="red"><b>root/</b></font></a><a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            } else if ($('#file-path a:last').text() === 'root/') {
                $('#root-a').after($('<a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            } else if ($('#file-path a:last').text() !== name) {
                $('#file-path a:last').remove();
                $('#root-a').after($('<a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            };
            data = JSON.stringify(name);
            ajax_res(data);
            $('#cons').on('click', function() {
                $('#add-information').append($('<p>Enter the info:</p><input type="text" id="constant" placeholder="constant" style="margin-bottom:5px;width:100%;margin-top:5px;"><input type="text" id="type" placeholder="type" style="margin-bottom:20px;width:100%;">'));
            });
            $('#them').on('click', function() {
                $('#add-information').append($('<p>Enter the info:</p><input type="text" id="thm" placeholder="theorem" style="margin-bottom:5px;width:100%;">'
        +'<input type="text" id="term" placeholder="term" style="margin-bottom:5px;width:100%;">'
        +'<input type="text" id="vars" placeholder="vars" style="margin-bottom:20px;width:100%;">'));
            });
            $('#datat').on('click', function() {
                $('#add-information').append($('<p>Enter the info:</p><input type="text" class="datatype" id="datatype" placeholder="datatype" style="margin-bottom:5px;width:100%;"><input type="text" class="datatype" id="args" placeholder="args" style="margin-bottom:5px;width:100%;"><input type="text" class="datatype" id="name1" placeholder="name1" style="margin-bottom:5px;width:50%;float:left;">'
        +'<input type="text" class="datatype" id="name2" placeholder="name2" style="margin-bottom:5px;width:50%;float:left;">'
        +'<input type="text" class="datatype" id="type1" placeholder="type1" style="margin-bottom:5px;width:50%;float:left;">'
        +'<input type="text" class="datatype" id="type2" placeholder="type2" style="margin-bottom:5px;width:50%;float:left;">'
        +'<input type="text" class="datatype" id="args1" placeholder="args1" style="margin-bottom:5px;width:50%;float:left;">'
        +'<input type="text" class="datatype" id="args2" placeholder="args2" style="margin-bottom:20px;width:50%;float:left;">'));
            });
            $('#fun').on('click',function() {
                $('#add-information').append($('<p>Enter the info:</p><input type="text" id="function" placeholder="fun" style="margin-bottom:5px;width:100%;">'
        +'<input type="text" id="function-type" placeholder="type" style="margin-bottom:5px;width:100%;">'
        +'<input type="text" id="function-vars1" placeholder="vars1" style="float:left;margin-bottom:5px;width:50%;">'
        +'<input type="text" id="function-vars2" placeholder="vars2" style="float:left;margin-bottom:5px;width:50%;">'
        +'<input type="text" id="function-prop1" placeholder="prop1" style="float:left;margin-bottom:5px;width:50%;">'
        +'<input type="text" id="function-prop2" placeholder="prop2" style=":float:left;margin-bottom:5px;width:50%;">'))
            } )
        });

        $('#json-button').on('click', function () {
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
            success: function (r) {
                $.each(r['theories'], function (i, val) {
                    num_root++;
                    $('#root-file').append($('<a href="#"  ' + 'id="' + num_root + '"><font color="#006000"><b>' + val + '</b></font></a></br>'));
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
        if (x === 3)
            return 'tvar';
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
        if (r_data['instructions'] !== undefined) {
            instructions = r_data['instructions'];
        }
        else {
            instructions = []
        }
        var event = {
            'id': get_selected_id(),
            'vars': r_data['vars'],
            'prop': r_data['prop'],
            'theory_name': theory_name,
            'thm_name': r_data['name']
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
            'theory_name': theory_name,
            'thm_name': r_data['name']
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

    // Display result_list on the left side of the page.
    function display_result_list() {
        var import_str = theory_imports.join('、');
        $('#left_json').empty();
        $('#left_json').append($('<div id="description"><p><font color="#0000FF"><span name="description"><font color="006633">'+ theory_desc + '</font></span><br>'+
        '<font color="#006000"><span name="imports"><font color="0000FF"><b>imports </b></font>'+ import_str + '</span></font></p></div>'));
//        result_他是后台json路由传递回来的数据也就是json文件的内容；利用他了可以扎到对应文件内部的description以及headeer、imports等信息；
//[]是列表
        var num = 0;
        for (var d in result_list) {
            num++;
            var ext = result_list[d];
            var ty = ext.ty;
            var name = ext.name;
            var depth = ext.depth;
            if (ty === 'def.ax') {
                var type = '';
                $.each(ext.type_hl, function (i, val) {
                    type = type + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                });
                $('#left_json').append($(
                    '<div><p id="data-'+ num +'"><font color="#006000"><span name="constant"><b>constant </b></span></font><tt><span name="name">' + name + '</span> :: <span name="content">' + type
                    + '</span></tt>&nbsp;&nbsp;&nbsp;<a href="#" name="edit" id="data-'+ num +'"><b>edit</b></a></p></div>'));
            }

            if (ty === 'thm') {
                var prop = '';
                $.each(ext.prop_hl, function (i, val) {
                    prop = prop + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                });
                var status_color;
                if (ext.proof === undefined) {
                    status_color = 'red'
                }
                else if (ext.num_gaps > 0) {
                    status_color = 'yellow'
                }
                else {
                    status_color = 'green'
                }
                $('#left_json').append($(
                    '<div><div style="float:left;width: 12px; height: 12px; background: ' +
                    status_color + ';">&nbsp;</div>' + '<p id="data-'+ num +'"><span name="theorem"><font color="#006000"><b>theorem</b></font></span> <span id="thm_name" name="name"><tt>' + name +
                    '</tt></span>:&nbsp;<a href="#" ' + 'id="' + num + '" name="proof">&nbsp;proof</a>&nbsp;&nbsp;<a href="#" name="edit" id="data-'+ num +'"><b>edit</b></a>' + '</br>&nbsp;&nbsp;<span name="content">' +
                    prop + '</span></p></div>'));
            }

            if (ty === 'type.ind') {
                var argsT = ext.argsT, constrs = ext.constrs;
                var str = '', type_name = '';
                $.each(argsT['concl'], function(k, vl){
                    type_name += '<tt class="' + rp(vl[1]) +'">'+ vl[0] + '</tt>'
                });
                $.each(constrs, function(i, v) {
                    var str_temp_var = '';
                    $.each(v.args, function(k, val) {
                        var str_temp_term = '';
                        $.each(argsT[i][k], function(l, vlu) {
                            str_temp_term += '<tt class="'+ rp(vlu[1]) + '">'+ vlu[0] +'</tt>';
                        });
                    str_temp_var += ' (' + val + ' :: '+ str_temp_term + ')';
                    })
                str += '</br>&nbsp;&nbsp;' + v['name'] + str_temp_var;
                })
                $('#left_json').append($(
                    '<div><p id="data-'+ num +'"><span name="datatype"><font color="#006000"><b>datatype</b></font></span> <span name="name">' + type_name + '</span> =<span name="content">' + str + '</span>&nbsp;&nbsp;&nbsp;<a href="#" name="edit" id="data-'+ num +'"><b>edit</b></a></p></div>'));
            }

            if (ty === 'def.ind') {
                var type = '';
                $.each(ext.type_hl, function (i, val) {
                    type = type + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                });
                $('#left_json').append($(
                    '<p id="data-' + num + '"><span name="fun"><font color="#006000"><b>fun</b></font></span> <span name="name">' + name + ' :: ' + type +
                    '</span><font color="#006000"><b> where</b></font></p>'));
                for (var j in ext.rules) {
                    var str = '';
                    $.each(ext.rules[j].prop_hl, function (i, val) {
                        str = str + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
                    });
                    $('#left_json p:last').append($('<span name="content"></br>&nbsp;&nbsp;' + str + '</span>'));
                }
                $('#left_json p#data-'+ num +' span[name="content"]:last').after($('<a href="#" name="edit" id="data-'+ num +'"><b>&nbsp;&nbsp;&nbsp;edit</b></a>'));

            }
            if (ty==='header') {
                $('#left_json').append($('<div><p id="data-'+ num +'">&nbsp;<span id="head_name" name="name">' +name + '</span><br>&nbsp;&nbsp;<a href="#" name="edit" id="data-' + num +'"><b>edit</b></a></p></div>'))
            }
        }
    }

    // Add new entry to the file.
    function add_info() {
        var item = {};
        if ($('#constant, #type').val() !== '') {
            var cons = $('#constant').val();
            var type = $('#type').val();
            item['ty'] = 'def.ax';
            item['name'] = cons;
            item['type'] = type;
            $('#constant,#type').val('');
        }

        if ($('#thm, #term, #vars').val() !== '') {
            var vars = {};
            var theo = $('#thm').val();
            var term = $('#term').val();
            var vars_str = $('#vars').val();
            var vars_list = vars_str.split(' ');  //  A:bool B:bool C:bool =>  ["A:bool","B:bool","C:bool"]
            for (var i in vars_list) {
                var v_list = vars_list[i].split(':');
                vars[v_list[0]] = v_list[1];
            }
            item['ty'] = 'thm';
            item['name'] = theo;
            item['vars'] = vars;
            item['prop'] = term;
            $('#thm,#term,#vars').val('');
        }
        var event = {
            "theory_name": theory_name,
            "item": item
        };

        data_ajax = JSON.stringify(event);
        $.ajax({
            url: "/api/add-info",
            type: "POST",
            data: data_ajax,
            success: function (result) {
                result_list = result_list.concat(result['data']);
                display_result_list();
            }
        });
    }

    $('#left_json').on('blur','textarea[name="edit"]', function(){
        var value = $(this).val();
        var ty = $(this).prev().text();
        var id = $(this).parent().attr('id')-1;
        $(this).replaceWith('<span name="constant" style="border:solid 0px;"> '+value+'</span>');
        event = {
            "name": name,//文件名 logicbase
            "data": value,//bool
            "ty": ty,//constant
            "n": id//
        }
        var data = JSON.stringify(event);
        $.ajax({
            url: '/api/save_edit',
            type: 'PUT',//Only send info ;
            data: data,
            success: function(){
                alert('save success!');
            }

        })
    })

    function ajax_res(data) {
        $.ajax({
            url: "/api/json",
            type: "POST",
            data: data,
            success: function (result) {
                theory_name = result['data']['name'];
                theory_imports = result['data']['imports'];
                theory_desc = result['data']['description'];
                result_list = result['data']['content'];
                display_result_list();
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
        cells[editor_id] = {};
        cells[editor_id].click_line_number = -1;
        cells[editor_id].ctrl_click_line_numbers = new Set();
        cells[editor_id].edit_line_number = -1;
        cells[editor_id].readonly_lines = [0];
        editor.on("keydown", function (cm, event) {
            let line_no = cm.getCursor().line;
            let line = cm.getLine(line_no);
            var id = get_selected_id();
            if (event.code === 'Enter') {
                event.preventDefault();
                if (cells[id].edit_line_number !== undefined && cells[id].edit_line_number !== -1) {
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
                if (cells[id].edit_line_number !== undefined && cells[id].edit_line_number !== -1) {
                    cm.getAllMarks().forEach(e => {
                        if (e.readOnly !== undefined) {
                            if (e.readOnly) {
                                e.clear();
                            }
                        }
                    });
                    var origin_line = display_line(cells[id]['proof'][cells[id].edit_line_number]);
                    cm.replaceRange(origin_line, {line: cells[id].edit_line_number, ch: 0}, {
                        line: cells[id].edit_line_number,
                        ch: Number.MAX_SAFE_INTEGER
                    });
                    cells[id].readonly_lines.push(cells[id].edit_line_number);
                    cells[id].readonly_lines.sort();
                    cells[id].edit_line_number = -1;
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
                apply_backward_step_thm(cm);
                is_mousedown = false;
                is_ctrl_click = false;
            }
        });

        editor.on('beforeChange', function (cm, change) {
            if (!edit_flag &&
                cells[get_selected_id()].readonly_lines.indexOf(change.from.line) !== -1) {
                change.cancel();
            }
        });

        editor.on('mousedown', function (cm, event) {
            var timer = 0;
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
        var id = get_selected_id();
        if (line.indexOf('sorry') !== -1) {
            cm.getAllMarks().forEach(e => {
                if (e.readOnly !== undefined)
                    if (e.readOnly)
                        e.clear();
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            cells[id].readonly_lines.splice(line_num, 1);
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch - 5}, {readOnly: true});
            cm.addSelection({line: line_num, ch: ch - 5}, {line: line_num, ch: ch});
            cells[id].edit_line_number = line_num;
        } else if (line.split(': ')[1].trim() === '') {
            cm.getAllMarks().forEach(e => {
                if (e.readOnly !== undefined)
                    if (e.readOnly)
                        e.clear();
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            cells[id].readonly_lines.splice(line_num, 1);
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {readOnly: true});
            cells[id].edit_line_number = line_num;
        }
    }

    function mark_text(cm) {
        var origin_pos = cm.getCursor();
        cm.setCursor(cm.getCursor().line, Number.MAX_SAFE_INTEGER);
        var line_num = cm.getCursor().line;
        var ch = cm.getCursor().ch;
        var line = cm.getLineHandle(line_num).text;
        var id = get_selected_id();
        var cell = cells[id] ? cells[id] : undefined;
        if (is_ctrl_click && cell.click_line_number !== undefined
            && cell.click_line_number !== -1 && line_num < cell.click_line_number) {
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {css: 'background: yellow'})
            cells[id].ctrl_click_line_numbers.add(line_num);
            is_ctrl_click = false;
        } else if (line.indexOf('sorry') !== -1) {
            cm.markText({line: line_num, ch: ch - 5}, {line: line_num, ch: ch}, {
                css: "background: red"
            });
            cells[id].click_line_number = line_num;
        } else {
            cm.getAllMarks().forEach(e => {
                if (e.css !== undefined)
                    if (e.css.indexOf('background') !== -1)
                        e.clear();
            });
            cells[id].click_line_number = -1;
            cells[id].ctrl_click_line_numbers.clear();
        }
        clear_match_thm();
        cm.setCursor(origin_pos);
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
