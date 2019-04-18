(function ($) {
    var instructions = [];
    var page_num = 0;
    var index = 0;
    var theory_name = "";  // Name of the current theory file
    var theory_imports = [];  // List of imports of the current theory file
    var result_list = [];  // Content of the current theory file
    var theory_desc = "";  // Description of the theory
    var is_fact = false;
    var click_count = 0;
    var proof_id = 0;
    var bgColor = '';
    var origin_result = [];
    var edit_mode = false;
    var result_list_dict = {};
    var file_list = [];
    var add_mode = false;
    var theories_selected = [];

    $(document).ready(function () {
        document.getElementById('left').style.height = (window.innerHeight - 40) + 'px';
    });

    $(document).ready(function () {
        var includes = $('[data-include]');
        jQuery.each(includes, function(){
            var file = "../" + $(this).data('include') + '.html';
            $(this).load(file);
        });
    });

    $(function () {
//      click add_cell to add a tab page;
        $('#add-cell').on('click', function () {
            page_num++;
            // Add CodeMirror textarea;
            var templ_tab = _.template($("#template-tab").html());
            $('#codeTab').append(templ_tab({page_num: page_num, label: ""}));

            let class_name = 'tab-pane fade active newCodeMirror code-cell';
            if (page_num === 1)
                class_name = 'tab-pane fade in active code-cell';
            $('#codeTabContent').append(
                $(`<div class="${class_name}" id="code${page_num}-pan"><label for="code${page_num}"></label> <textarea id="code${page_num}"></textarea>${$('div.rbottom').append(
                    '<div id="prf' + page_num + '" name="addition"><button id="' + proof_id + '" class="el-button el-button--default el-button--mini save_proof" style="margin-top:5px;width:100px;margin-left:25px;" name="save"' + theory_name + '><b>SAVE</b></button>' +
                    '<button id="' + proof_id + '" class="el-button el-button--default el-button--mini reset" style="margin-top:5px;width:100px;" name="reset' + theory_name + '"><b>RESET</b></button></div>')}`));
            init_editor("code" + page_num);
            // Add location for displaying results;
            $('div#prf' + page_num).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<pre> </pre></div><div class="match-thm"">' +
                    '<div class="abs-thm"></div>' +
                    '<div class="rewrite-thm"></div>' +
                    '<div class="afs-thm"></div>' +
                    '<div class="clear"></div>' +
                    '</div></div>'));
            $('div#prf' + page_num).append(
                $('<div class="output-wrapper"><div class="output"><div class="output-area">' +
                    '<a href="#" id="link-backward" style="float:left;"><</a>' +
                    '<pre id="instruction-number", style="float:left;"> </pre>' +
                    '<a href="#" id="link-forward" style="float:left;">></a>' +
                    '<pre id="instruction" style="float:left;"> </pre></div></div>'));
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
            $('div#prf' + page_num).show().siblings().hide();
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active');
            });
        });

        $('#right').on('click', '.backward-step', function () {
            apply_backward_step(get_selected_editor(), is_others = true);
        });

        $('#right').on('click', ' .abs-thm .thm-content pre', function () {
            apply_backward_step(get_selected_editor(), is_others = false, select_thm = $(this).index());
        });

        $('#right').on('click', '.forward-step', function () {
            apply_forward_step(get_selected_editor(), is_others = true);
        });

        $('#right').on('click', ' .afs-thm .thm-content pre', function () {
            apply_forward_step(get_selected_editor(), is_others = false, select_thm = $(this).index());
        });

        $('#right').on('click', '.rewrite-goal', function () {
            rewrite_goal(get_selected_editor(), is_others = true);
        });

        $('#right').on('click', ' .rewrite-thm .thm-content pre', function () {
            rewrite_goal(get_selected_editor(), is_others = false, select_thm = $(this).index());
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

        $('#add-json').click(function () {
            page_num++;
            init_metadata_area(page_num);
        });

        function init_metadata_area(add_page) {
            var templ_tab = _.template($("#template-tab").html());
            $('#codeTab').append(templ_tab({page_num: add_page, label: "File"}));

            let class_name = 'tab-pane fade active newCodeMirror code-cell';
            if (add_page === 1)
                class_name = 'tab-pane fade in active code-cell';

            var templ_form = _.template($('#template-file-metadata').html());
            $('#codeTabContent').append(templ_form({class_name: class_name, add_page: add_page}));

            $('div.rbottom').append(
                '<div id="prf' + add_page + '" name="addition"><button id="' + add_page + '" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:100px;margin-left:25px;" name="save-json"><b>SAVE</b></button>' +
                '</div>');
            $('#codeTab a[href="#code' + add_page + '-pan"]').tab('show');
            $('div#prf' + add_page).addClass('selected').siblings().removeClass('selected');
            $('div#prf' + add_page).show().siblings().hide();
            $('.newCodeMirror').each(function () {
                $(this).removeClass('active');
            });
        }

//      click save to create and save json_file metadata;
        $('div.rbottom').on('click', 'button[name="save-json"]', function () {
            var pnum = $(this).attr('id');
            var fname = $('#fname' + pnum).val().trim();
            var imp = $('#imp' + pnum).val().split(',');
            var des = $('#code' + pnum).val().trim();
            var flag = false;
            $.each(file_list, function (i, v) {
                if (v === fname)
                    flag = true;
            });
            if (flag === false)
                file_list.push(fname);
            file_list.sort();
            data = {
                'name': fname,
                'imports': imp,
                'description': des
            };
            $.ajax({
                url: '/api/add-new',
                type: 'PUT',
                data: JSON.stringify(data),
                success: function (res) {
                    alert('保存成功!');
                    display_file_list();
                }
            })
        });

//      tab on the left;
        $('#json-tab1,#json-tab2,#json-tab3').click(function () {
            $(this).css({'background': '	#F0F0F0', 'text-align': 'center', 'border-bottom': 'none'});
            $(this).siblings('li').css({
                'background': '#f8f8f8',
                'text-align': 'center',
                'border-bottom': 'solid 1px',
                'border-color': '#B8B8B8'
            });
        });

        $('#json-tab1').click(function () {
            $('div#root-file').show();
            $('div#left_json').hide();
            $('div#varible').hide();
        });

        $('#json-tab2').click(function () {
            $('div#root-file').hide();
            $('div#left_json').show();
            $('div#varible').hide();
        });

        $('#json-tab3').click(function () {
            $('div#root-file').hide();
            $('div#left_json').hide();
            $('div#varible').show();
        });

        $('div#root-file').on('click', 'a[name="edit"]', function () {
            var number = Number($(this).attr('id').slice(4,).trim()) - 1;
            page_num++;
            data = JSON.stringify(file_list[number]);
            init_metadata_area(page_num);
            $.ajax({
                url: '/api/edit_jsonFile',
                data: data,
                type: 'POST',
                success: function (res) {
                    var name = res['name'];
                    var des = res['description'];
                    var imports = res['imports'].join(',');
                    $('input#fname' + page_num).val(name);
                    $('input#imp' + page_num).val(imports);
                    $('textarea#code' + page_num).val(des);
                }
            })
        });

        $('div#root-file').on('click', 'a[name="delete"]', function () {
            var number = Number($(this).attr('id').trim()) - 1;
            var json_name = $(this).attr('class');
            file_list.splice(number, 1);
            display_file_list();
            save_file_list(json_name);
        });

        $('button#register').click(function() {
            $.ajax({
                url: '/api/register',
                type: 'GET',
                success: function() {
                }
            })
        })

        // Save a single proof to the webpage (not to the json file);
        $('div.rbottom').on('click', 'button.save_proof', function () {
            editor_id_list = [];
            var file_name = $(this).attr('name').slice(4,);
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
            });
            result_list[id]['proof'] = output_proof;
            result_list[id]['num_gaps'] = cells[editor_id]['num_gaps'];
            result_list_dict[file_name] = result_list;
            display_result_list();
            save_json_file();
        });

        function result_to_output(data) {
            if (data.ty === 'def.ax') {
                delete data.type_hl;
            } else if (data.ty === 'thm' || data.ty === 'thm.ax') {
                delete data.prop_hl;
            } else if (data.ty === 'type.ind') {
                delete data.argsT;
                delete data.ext;
            } else if (data.ty === 'def') {
                delete data.term;
                delete data.type_hl;
            } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
                delete data.type_hl;
                delete data.ext;
                for (var i in data.rules) {
                    delete data.rules[i].prop_hl;
                }
            }
        }

//      save all of the edited_tab_data to the json-file;
        function save_editor_data() {
            var copy_res = $.extend(true, [], result_list);
            display_result_list();
            $.each(copy_res, function (i, v) {
                result_to_output(v);
            });
            $.ajax({
                url: '/api/editor_file',
                type: 'PUT',
                data: JSON.stringify({
                    'name': name,
                    'data': copy_res
                }),
                success: function () {
                }
            })
        }

        // Save all changed proof on the webpage to the json-file;
        function save_json_file() {
            var output_list = [];
            for (var d in result_list) {
                output_list[d] = {};
                $.extend(output_list[d], result_list[d]);  // perform copy
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
            };
            $.ajax({
                url: "/api/save_file",
                type: "POST",
                data: JSON.stringify(data),
                success: function () {
                }
            });
        }

        //click reset button to reset the thm to the origin status;
        $('div.rbottom').on('click', 'button.reset', function () {
            var id = Number($(this).attr('id')) - 1;
            var file_name = $(this).attr('name').slice(5,);
            if (file_name) {
                theorem_proof(result_list_dict[file_name][id], file_name);
            }
        });

//      click the tab to show;
        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            var tab_pm = $(this).attr('name');
            $(this).tab('show');
            $('div#prf' + tab_pm).addClass('selected').siblings().removeClass('selected');
            $('div#prf' + tab_pm).show().siblings().hide();
        });

//      set cursor & size;
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

//      click x on the tab to close and delete the related tab page;
        $('#codeTab').on('click', 'li button', function () {
            var tabId = $(this).parents('li').children('a').attr('href');
            if ($(this).attr('name') === 'code' + tab_pm)
                var id = get_selected_id();
            delete cells[id];
            var tab_pm = $(this).parents('li').attr('name').slice(4,);
            $('div#prf' + tab_pm).remove();
            $(this).parents('li').remove('li');
            $(tabId).remove();
            $('#codeTab a:first').tab('show');
            $('div.rbottom div:eq(0)').addClass('selected').siblings().removeClass('selected');
            $('div.rbottom div:eq(0)').show().siblings().hide();
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

        //click proof then send it to the init; including the save-json-file;
        $('#left_json').on('click', 'a[name="proof"]', function (e) {
            e.stopPropagation();
            proof_id = $(this).attr('id');
            eidt_mode = false;
            var thm_name = $(this).parent().find('span#thm_name').text();
            if (result_list[proof_id - 1]['proof']) {
                $('#add-cell').click();
                setTimeout(function () {
                    $('#codeTab li[name="' + get_selected_id() + '"] span').text(thm_name);
                    init_saved_proof(result_list[proof_id - 1]);
                }, 200);
            } else {
                $('#add-cell').click();
                setTimeout(function () {
                    $('#codeTab li[name="' + get_selected_id() + '"] span').text(thm_name);
                    theorem_proof(result_list[proof_id - 1], theory_name);
                }, 200);
            }
        });

//      click edit then create a tab page for the editing;
        $('#left_json').on('click', 'a[name="edit"]', function () {
            page_num++;
            edit_mode = true;
            var a_ele = $(this);
            init_edit_area(page_num, a_ele);
        });

//      click delete then delete the content from webpage;
        $('#left_json').on('click', 'a[name="del"]', function () {
            var a_id = $(this).attr('id').trim();
            var number = Number(a_id.slice(5,)) - 1;
            result_list.splice(number, 1);
            display_result_list();
            save_editor_data();
            alert('删除成功！');
        });

//      keypress to display unicode;
        $('#codeTabContent').on('keydown', 'textarea,input', function (e) {
            var content = $(this).val().trim();
            var id = $(this).attr('id');
            var pos = document.getElementById(id).selectionStart;
            if (pos !== 0 && e.keyCode === 9) {
                if (e && e.preventDefault) {
                    e.preventDefault();
                } else {
                    window.event.returnValue = false;
                }
                for (var key in replace_obj) {
                    l = key.length;
                    if (content.substring(pos - l, pos) === key) {
                        var len = l;
                        content = content.slice(0, pos - l) + replace_obj[key] + content.slice(pos,);
                    }
                }
                $(this).val(content);
                document.getElementById(id).setSelectionRange(pos - len + 1, pos - len + 1);
            }
        });

//      set the textarea height auto; press tab display unicode;
        $('#codeTabContent').on('input', 'textarea', function () {
            var rows = $(this).val().split('\n').length + 1;
            $(this).attr('rows', rows);
        });

        function change_css(obj) {
            if (obj.length > 0) {
                var rows = obj.val().split('\n').length + 1;
                obj.attr('rows', rows);
            }
        }

//      the method for add_info && edit_info;
        function init_edit_area(page_num, a_ele = '', data_type = '') {
            var a_id, data_name = '', data_content = '', vars_str = '', data_label,
                border = '1px;solid #ffffff;border:none';
            var class_name = 'tab-pane fade in active code-cell edit-data';
            if (!a_ele) {
                a_id = '', border = '', data_name = '', data_content = '', number = '', data_label = data_type;
            } else {
                a_id = a_ele.attr('id').trim();
                number = String(Number(a_id.slice(5,)) - 1);
                data_name = result_list[number]['name'];
                data_type = result_list[number]['ty'];
                data_label = data_name;
                for (var key in result_list[number]['vars']) {
                    vars_str += key + ':' + result_list[number]['vars'][key] + '\n';
                }
            }

            var templ_tab = _.template($("#template-tab").html());
            $('#codeTab').append(templ_tab({page_num: page_num, label: data_label}));

            if (data_type === 'def.ax') {
                if (number)
                    data_content = result_list[number]['type'];
                else
                    $('#codeTab').find('span#' + page_num).text('constant');

                var templ_edit = _.template($("#template-edit-def-ax").html());
                $('#codeTabContent').append(templ_edit({
                    a_id: a_id, class_name: class_name, page_num: page_num,
                    border: border, data_name: data_name, data_content: data_content
                }));
                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'thm' || data_type === 'thm.ax') {
                if (data_type === 'thm')
                    var type_name = 'theorem';
                else
                    var type_name = 'axiom';
                if (number)
                    data_content = result_list[number]['prop'];

                var templ_edit = _.template($('#template-edit-thm').html());
                $('#codeTabContent').append(templ_edit({
                    a_id: a_id, class_name: class_name, type_name: type_name, page_num: page_num,
                    border: border, data_name: data_name, vars_str: vars_str, data_content: data_content
                }));

                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'type.ind') {
                if (number) {
                    var ext = result_list[number]['ext'];
                    var argsT = result_list[number]['argsT'];
                    var ext_ = '';
                    $.each(ext, function (i, v) {
                        ext_ += v[0][1] + '  ' + v[1] + ':' + v[0][0] + '\n';
                    });
                    data_name = '';
                    $.each(argsT.concl, function (i, j) {
                        data_name += j[0];
                    });
                    $.each(result_list[number]['constrs'], function (i, v) {
                        var str_temp_var = '';
                        $.each(v.args, function (k, val) {
                            var str_temp_term = '';
                            $.each(argsT[i][k], function (l, vlu) {
                                str_temp_term += vlu[0];
                            });
                            str_temp_var += ' (' + val + ' :: ' + str_temp_term + ')';
                        });
                        data_content += '\n' + v['name'] + str_temp_var;
                    })
                } else
                    $('#codeTab').find('span#' + page_num).text('datatype');
                data_content = $.trim(data_content);
                var i = data_content.split('\n').length;
                $('#codeTab').find('span#' + page_num).text(data_name);

                var templ_edit = _.template($('#template-edit-type-ind').html());
                $('#codeTabContent').append(templ_edit({
                    a_id: a_id, class_name: class_name, page_num: page_num,
                    border: border, data_name: data_name, i: i, data_content: data_content,
                    ext_: ext_}));

                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            }
            if (data_type === 'def.ind' || data_type === 'def.pred' || data_type === 'def') {
                var data_content_list = [];
                var data_new_content = '';
                var data_rule_names = [], data_rule_name = '';
                if (data_type === 'def.ind')
                    var type_name = 'fun';
                else if (data_type === 'def.pred')
                    var type_name = 'inductive';
                else
                    var type_name = 'definition'

                if (number) {
                    var ext = result_list[number];
                    var ext_ = ext.ext;
                    var ext_str = '';
                    var vars = '';
                    $.each(ext_, function (i, v) {
                        ext_str += v[0][1] + '  ' + v[1] + ':' + v[0][0] + '\n';
                    });
                    data_name = ext.name + ' :: ' + ext.type;
                    if (ext.rules) {
                        for (var j in ext.rules) {
                            var data_con = '';
                            $.each(ext.rules[j].prop_hl, function (i, val) {
                                data_con += val[0];
                            });
                            data_content_list.push(data_con);
                            data_rule_names.push(ext.rules[j]['name']);
                        }
                    }
                    if (data_type === 'def') {
                        var i = 0;
                        data_content_list.push(ext.prop);
                        for (v in ext.vars) {
                            vars += i + ': ' + v + ':' + ext.vars[v] + '\n';
                            i++;
                        }
                    }
                    for (var i in data_content_list) {
                        data_new_content += i + ': ' + data_content_list[i] + '\n';
                        data_rule_name += i + ': ' + data_rule_names[i] + '\n';
                    }
                    $('#codeTab').find('span#' + page_num).text(ext.name);
                } else
                    $('#codeTab').find('span#' + page_num).text('function');

                var templ_edit = _.template($('#template-edit-def').html());
                $('#codeTabContent').append(templ_edit({
                    a_id: a_id, class_name: class_name, page_num: page_num,
                    type_name: type_name, border: border, data_name: data_name,
                    data_new_content: data_new_content, vars: vars, ext_str: ext_str
                }));

                $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
                if (data_type === 'def.pred') {
                    $('textarea#data-vars' + page_num).after('<br><textarea rows="' + data_rule_name.split('\n').length + '" spellcheck="false" id="data-names' + page_num + '" style="overflow-y:hidden;margin-top:5px;width:60%;background:transparent;' + border + '" name="names">' + $.trim(data_rule_name) + '</textarea>')
                }
                if (data_type !== 'def')
                    display_lines_number(data_content_list, page_num, number);
            }

            if (number && 'hint_backward' in result_list[number] && result_list[number]['hint_backward'] === 'true')
                $('input[name="hint_backward' + page_num + '"]').click();
            if (number && 'hint_rewrite' in result_list[number] && result_list[number]['hint_rewrite'] === 'true')
                $('input[name="hint_rewrite' + page + '"]').click();
            change_css($('textarea#data-vars' + page_num));
            change_css($('textarea#data-content' + page_num));
            change_css($('textarea#data-names' + page_num));
            $('div.rbottom').append('<div id="prf' + page_num + '"><button id="save-edit" name="' + data_type + '" class="el-button el-button--default el-button--mini" style="margin-top:5px;width:20%;"><b>SAVE</b></button></div>');
            $('div#prf' + page_num).append(
                '<div class="output-wrapper" style="margin-top:15px;margin-left:40px;" id="error' + page_num + '">' +
                '<pre></pre></div>');
            $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
            $('div#prf' + page_num).show().siblings().hide();
        }

//      display vars_content in the textarea;
        function display_lines_number(content_list, page_num, number) {
            var data_vars_list = [];
            var data_vars_str = '';
            if (number) {
                $.each(result_list[number]['rules'], function (i, v) {
                    var vars_str = '';
                    for (let key in v.vars) {
                        vars_str += key + ':' + v.vars[key] + '   ';
                    }
                    data_vars_list.push(vars_str);
                });
                $.each(data_vars_list, function (i, v) {
                    data_vars_str += i + ': ' + v + '\n';
                })
            } else {
                data_vars_str += '';
            }
            $('textarea#data-vars' + page_num).val($.trim(data_vars_str));
        }

//      click save button on edit tab to save content to the left-json for updating;
        $('div.rbottom').on('click', 'button#save-edit', function () {
            var tab_pm = $(this).parent().attr('id').slice(3,);
            var a_id = $('div#code' + tab_pm + '-pan').attr('name').trim();
            var error_id = $(this).next().attr('id').trim();
            var id = tab_pm;
            var ty = $(this).attr('name').trim();
            var number = Number(a_id.slice(5,)) - 1;
            var ajax_data = make_data(ty, id, number);
            var prev_list = result_list.slice(0, number);
            if ($('input[name="hint_backward' + tab_pm + '"]').prop('checked') === true)
                result_list[number]['hint_backward'] = 'true';
            else if (number !== -1 && 'hint_backward' in result_list[number])
                delete result_list[number]['hint_backward'];
            if ($('input[name="hint_rewrite' + tab_pm + '"]').prop('checked') === true)
                result_list[number]['hint_rewrite'] = 'true';
            else if (number !== -1 && 'hint_rewrite' in result_list[number])
                delete result_list[number]['hint_rewrite'];
            ajax_data['file-name'] = name;
            ajax_data['prev-list'] = prev_list;
            $.ajax({
                url: '/api/save_modify',
                type: 'POST',
                data: JSON.stringify(ajax_data),
                success: function (res) {
                    var result_data = res['data'];
                    var data_name = result_data['name'];
                    var error = res['error'];
                    delete result_data['file-name'];
                    delete result_data['prev-list'];
                    if (error && error !== {}) {
                        var error_info = error['detail-content'];
                        $('div#' + error_id).find('pre').text(error_info);
                    }
                    if (!a_id) {
                        result_list.push(result_data);
                    } else {
                        for (var key in result_data) {
                            result_list[number][key] = result_data[key];
                        }
                    }
                    display_result_list();
                    save_editor_data();
                    alert('保存成功！')
                }
            });
        });

//      make a strict-type data from editing; id=page_num
        function make_data(ty, id, number) {
            var data_name = $('#data-name' + id).val().trim();
            var data_content = $('#data-content' + id).val().trim();
            var ajax_data = {};
            if (ty === 'def.ax') {
                ajax_data['ty'] = 'def.ax';
                ajax_data['name'] = data_name;
                ajax_data['type'] = data_content;
            }
            if (ty === 'thm' || ty === 'thm.ax') {
                var vars_str_list = $('textarea#data-vars' + id).val().split('\n');
                var vars_str = {};
                ajax_data['ty'] = ty;
                ajax_data['name'] = data_name;
                ajax_data['prop'] = data_content;
                $.each(vars_str_list, function (i, v) {
                    let v_list = v.split(':');
                    vars_str[v_list[0]] = v_list[1];
                });
                ajax_data['vars'] = vars_str;
            }
            if (ty === 'type.ind') {
                var temp_list = [], temp_constrs = [];
                var temp_content_list = data_content.split(/\n/);
                if (data_name.split(/\s/).length > 1) {
                    temp_list.push(data_name.split(/\s/)[0].slice(1,));
                    ajax_data['name'] = data_name.split(/\s/)[1];
                } else {
                    ajax_data['name'] = data_name;
                }
                $.each(temp_content_list, function (i, v) {
                    var temp_con_list = v.split(') (');
                    var temp_con_dict = {};
                    var arg_name = '', args = [], type = '';
                    if (temp_con_list[0].indexOf('(') > 0) {
                        arg_name = temp_con_list[0].slice(0, temp_con_list[0].indexOf('(') - 1);
                        if (temp_con_list.length > 1) {
                            temp_con_list[0] = temp_con_list[0].slice(temp_con_list[0].indexOf('(') + 1,);
                            temp_con_list[temp_con_list.length - 1] = temp_con_list[temp_con_list.length - 1].slice(0, -1);
                            $.each(temp_con_list, function (i, v) {
                                args.push(v.split(' :: ')[0]);
                                type += v.split(' :: ')[1] + '⇒';
                                if (v.split(' :: ')[1].indexOf('⇒') >= 0) {
                                    type += '(' + v.split(' :: ')[1] + ')' + '⇒'
                                }
                            });
                            type = type + data_name;
                        } else {
                            let vars_ = temp_con_list[0].slice(temp_con_list[0].indexOf('(') + 1, -1).split(' :: ')[0];
                            type = temp_con_list[0].slice(temp_con_list[0].indexOf('(') + 1, -1).split(' :: ')[1];
                            args.push(vars_);
                            type = type + '=>' + data_name;
                        }
                    } else {
                        arg_name = temp_con_list[0];
                        type = ajax_data['name'];
                    }
                    temp_con_dict['type'] = type;
                    temp_con_dict['args'] = args;
                    temp_con_dict['name'] = arg_name;
                    temp_constrs.push(temp_con_dict);
                });
                ajax_data['ty'] = 'type.ind';
                ajax_data['args'] = temp_list;
                ajax_data['constrs'] = temp_constrs;
            }
            if (ty === 'def.ind' || ty === 'def' || ty === 'def.pred') {
                var rules_list = [];
                var rules = result_list[number].rules;
                var props_list = data_content.split(/\n/);
                var vars_list = $('textarea#data-vars' + id).val().trim().split(/\n/);
                if (ty === 'def.pred')
                    var names_list = $('textarea#data-names' + id).val().trim().split(/\n/);
                $.each(props_list, function (i, v) {
                    props_list[i] = $.trim(v.slice(3,));
                    vars_list[i] = $.trim(vars_list[i].slice(3,));
                    if (names_list)
                        names_list[i] = $.trim(names_list[i].slice(3,));
                });
                $.each(props_list, function (i, v) {
                    var temp_dict = {}, temp_vars = {};
                    if (v && vars_list[i]) {
                        temp_dict['prop'] = v;
                        $.each(vars_list[i].split(/\s\s/), function (j, k) {
                            temp_vars[$.trim(k.split(':')[0])] = $.trim(k.split(':')[1]);
                        });
                        if (names_list)
                            temp_dict['name'] = names_list[i];
                    } else if (!v) {
                        return true;
                    }
                    temp_dict['vars'] = temp_vars;
                    rules_list.push(temp_dict);
                });
                if (ty !== 'def')
                    ajax_data['rules'] = rules_list;
                else
                    ajax_data['vars'] = temp_vars;
                ajax_data['ty'] = ty;
                ajax_data['name'] = data_name.split(' :: ')[0];
                ajax_data['type'] = data_name.split(' :: ')[1];
            }
            return ajax_data;
        }

//click to change left_json content bgcolor
        $('#left_json').on('click','div[name="theories"]',function(){
            var id = $(this).attr('id').trim();
            if ($(this).css('background-color') === bgColor) {
                $(this).css('background-color', '');
                var index = theories_selected.indexOf(id);
                theories_selected.splice(index, 1);
            }
            else {
                $(this).css('background-color','yellow');
                bgColor = $(this).css('background-color');
                console.log(bgColor);
                theories_selected.push(id);
            }
        })

//click DEL to delete red left_json content and save to webpage and json file
        $('div.dropdown-menu.Ctrl a[name="del"]').on('click',function(){
            var flag = true;
            $.each(theories_selected, function (i, v) {
              //if($(v).css('background-color') === bgColor)){
                 //var a_id = $('div[name="theories"]').attr('id').trim();
                   var number = Number(v.slice(3,))-1;//3是因为aa_是3个
                   result_list.splice(number, 1);
                   display_result_list();
                   flag = false;
                   //save_editor_data();
            })
            if(flag === false){
                alert('删除成功！');//为了避免在each中循环打印alert，可以使用flag标记
            }
            theories_selected = [];//这里必须清空一下，因为每次删除以后id值所代表的div会变化
        })
//        $('div.dropdown-menu.Ctrl a[name="up"]').on('click',function(){
//            if($('div[name="theories"]').css('background-color') === bgColor){
//                var a_id = $('div[name="theories"]').attr('id').trim();
//                var number = Number(a_id.slice(3,))-2;
//                result_list.splice(number, 1);
//                }})


//      click to save the related data to json file: edit && proof;
        $('a#save-file').click(function () {
            if (edit_mode) {
                save_editor_data();
            } else {
                save_json_file();
            }
        });

//      click to display json file;
        $('#root-file').on('click', 'a[name="file"]', function () {
            num = 0;
            $(this).parent().hide();
            $('#json-tab2').click();
            $('#left_json').empty();
            name = $(this).text();
            name = $.trim(name);
            if ($('#file-path').html() === '') {
                $('#file-path').append($('<a href="#" id="root-a"><font color="red"><b>root/</b></font></a><a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            } else if ($('#file-path a:last').text() === 'root/') {
                $('#root-a').after($('<a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            } else if ($('#file-path a:last').text() !== name) {
                $('#file-path a:last').remove();
                $('#root-a').after($('<a href="#"><font color="red"><b>' + name + '</b></font></a>'));
            }
            data = JSON.stringify(name);
            ajax_res(data);
            add_mode = true;
        });

        $('div.dropdown-menu.add-info a').on('click', function () {
            if (add_mode === true) {
                page_num++;
                edit_mode = true;
                var ty = $(this).attr('name');
                init_edit_area(page_num, '', ty);
            }
        });

        $('#json-button').on('click', function () {
            num = 0;
            $('#left_json').empty();
            name = prompt('please enter the file name');
            var data = JSON.stringify(name);
            ajax_res(data);
        });

        // On loading page, retrieve list of theories from root file.
        num_root = 0;
        $.ajax({
            url: "/api/find_files",
            success: function (r) {
                $('#json-tab1').click();
                file_list = r['theories'];
                display_file_list();
            }
        });
    });

    function display_file_list() {
        $('#root-file').html('');
        var templ = _.template($("#template-file-list").html());
        $('#root-file').append(templ({file_list: file_list}));
    }

    function save_file_list(file_name) {
        $.ajax({
            url: '/api/save_file_list',
            data: JSON.stringify(file_name),
            type: 'PUT',
            success: function (res) {
                alert('删除成功！');
            }
        })
    }

    function theorem_proof(r_data, the_name) {
        if (r_data['instructions'] !== undefined) {
            instructions = r_data['instructions'];
        } else {
            instructions = []
        }
        var event = {
            'id': get_selected_id(),
            'vars': r_data['vars'],
            'prop': r_data['prop'],
            'theory_name': the_name,
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
        result_list_dict[theory_name] = result_list;
        var import_str = theory_imports.join(' ');
        $('#left_json').html('');
        var templ = _.template($("#template-content-theory_desc").html());
        $('#left_json').append(templ({theory_desc: theory_desc, import_str: import_str}));
        $.each(result_list, function(num, ext) {
            var templ = $("#template-content-" + ext.ty.replace(".", "-"));
            if (templ.length == 1) {
                $('#left_json').append(_.template(templ.html())({num: num+1, ext: ext}));
            }
        });
    }

//  display_hilight;
    function ajax_res(data) {
        $.ajax({
            url: "/api/json",
            type: "POST",
            data: data,
            success: function (result) {
                var error = result['error'];
                theory_name = result['data']['name'];
                theory_imports = result['data']['imports'];
                theory_desc = result['data']['description'];

                if (theory_name in result_list_dict) {
                    result_list = result_list_dict[theory_name];
                } else
                    result_list = result['data']['content'];
                display_result_list();
            }
        });
    }

    function init_editor(editor_id = "code1") {
        var id = editor_id;
//        var cell = cells[id]['proof'];
        var editor = CodeMirror.fromTextArea(document.getElementById(editor_id), {
            mode: "text/x-python",
            lineNumbers: true,
            firstLineNumber: 0,
            lineNumberFormatter: function (line) {
                return line;
            },
            theme: "",
            lineWrapping: false,
            foldGutter: true,
            smartIndent: false,
            matchBrackets: true,
            viewportMargin: Infinity,
            scrollbarStyle: "overlay",
            gutters: ["CodeMirror-linenumbers", "CodeMirror-foldgutter"],
            extraKeys: {
                "Ctrl-I": introduction,
                "Ctrl-B": apply_backward_step,
                "Ctrl-R": rewrite_goal,
                "Ctrl-F": apply_forward_step,
                "Ctrl-Q": function (cm) {
                    cm.foldCode(cm.getCursor());
                }
            }
        });
        var rtop = document.querySelector('.rtop');
        editor.setSize("auto", rtop.clientHeight - 40);
        editor.setValue("");
        cells[editor_id] = {};
        cells[editor_id].click_line_number = -1;
        cells[editor_id].facts = new Set();
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
                if (line.trim() === '') {
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
            if (!(undefined !== cm.target && undefined !== cm.facts)) {
                return;
            }
            is_mousedown = true;
            cm.setCursor(cm.target, 0);
            cm.facts.forEach(val => {
                is_mousedown = true;
                is_fact = true;
                cm.setCursor(val, 0);
            });
            delete cm.target;
            delete cm.facts;
        });

        editor.on('blur', function (cm, event) {
            var id = get_selected_id();
            var target = cells[id].click_line_number;
            var facts = [];
            for (const val of cells[id].facts) {
               facts.push(val);
            }
            cm.target = target;
            cm.facts = facts;
        });

        editor.on("cursorActivity", function (cm) {
            if (is_mousedown) {
                mark_text(cm);
                apply_thm(cm);
                is_mousedown = false;
                is_fact = false;
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
            if (exisit_fact(cm))
                is_fact = true;
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
        } else if (line.trim() === '') {
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
        if (is_fact && cell.click_line_number !== undefined
            && cell.click_line_number !== -1 && line_num < cell.click_line_number) {
            cm.markText({line: line_num, ch: 0}, {line: line_num, ch: ch}, {css: 'background: yellow'});
            cells[id].facts.add(line_num);
            is_fact = false;
        } else if (line.indexOf('sorry') !== -1) {
            if (cell.click_line_number !== undefined && cell.click_line_number !== -1) {
                cm.getAllMarks().forEach(e => {
                    if (e.css !== undefined)
                        if (e.css.indexOf('background: red') !== -1)
                            e.clear();
                });
            }
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
            cells[id].facts.clear();
        }

        clear_match_thm();
        cm.setCursor(origin_pos);
    }

    function exisit_fact(cm) {
        var id = get_selected_id();
        return cells[id].click_line_number !== -1;
    }

    function resize_editor() {
        var editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
        var rtop = document.querySelector('.rtop');
        editor.setSize("auto", rtop.clientHeight - 40);
        editor.refresh();
    }

    Split(['.rtop', '.rbottom'], {
        sizes: [70, 50],
        direction: 'vertical',
        minSize: 39,
        onDrag: resize_editor,
        gutterSize: 2,
    });
    Split(['.left', '.right'], {
        sizes: [30, 70],
        gutterSize: 2,
    });
})(jQuery);