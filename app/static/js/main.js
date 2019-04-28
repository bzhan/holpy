(function ($) {
    var selected_tab = 'files';   // Selected tab on the left side.
    var page_num = 0;   // Number of tabs opened on the right side.
    var instructions = [];
    var index = 0;
    var click_count = 0;
    var cur_theory_name = "";  // Name of the current theory file.
    var json_files = {};  // All loaded theory data.
    var file_list = [];  // List of all files for the current user.
    var items_selected = [];  // List of selected items in the displayed theory.

    $(function () {
        document.getElementById('left').style.height = (window.innerHeight - 40) + 'px';

        // Load html templates
        var includes = $('[data-include]');
        jQuery.each(includes, function () {
            var file = "../" + $(this).data('include') + '.html';
            $(this).load(file);
        });

        $('#right').on('click', '.other-step', function () {
            apply_thm_tactic(select_thm = -1, func_name = this.name);
        });

        $('#right').on('click', '.thm-content pre', function () {
            apply_thm_tactic(select_thm = $(this).index(), func_name = this.className);
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

        // Add new json file.
        $('#new-file').click(init_metadata_area);

        // Save metadata for json file.
        $('div.rbottom').on('click', 'button[name="save-metadata"]', function () {
            var form = get_selected_edit_form('edit-form');
            var fname = form.fname.value.trim();
            var imports = form.imports.value.split(',');
            var description = form.description.value.trim();
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
                'imports': imports,
                'description': description
            };
            $.ajax({
                url: '/api/save-metadata',
                type: 'PUT',
                data: JSON.stringify(data),
                success: function () {
                    alert('Saved file ' + fname);
                    display_file_list();
                }
            })
        });

        // Tabs on the left
        $('#json-tab-files,#json-tab-content,#json-tab-proof').click(function () {
            $(this).css({'background': '#F0F0F0', 'text-align': 'center', 'border-bottom': 'none'});
            $(this).siblings('li').css({
                'background': '#f8f8f8',
                'text-align': 'center',
                'border-bottom': 'solid 1px',
                'border-color': '#B8B8B8'
            });
            selected_tab = $(this).attr('id').slice(9,);
            $('div.left-panel').hide();
            $('div#panel-' + selected_tab).show();
        });

        // Edit metadata for a file
        $('div#panel-files').on('click', 'a[name="edit"]', function () {
            // File's id is "edit{n}"
            var number = Number($(this).attr('id').slice(4,).trim());

            data = JSON.stringify(file_list[number]);
            init_metadata_area();
            var form = document.getElementById('edit-metadata-form' + page_num);
            $.ajax({
                url: '/api/get-metadata',
                data: data,
                type: 'POST',
                success: function (res) {
                    form.fname.value = res.name;
                    form.imports.value = res.imports.join(',');
                    form.description.textContent = res.description;
                    form.description.rows = 5;
                }
            })
        });

        $('div#panel-files').on('click', 'a[name="delete"]', function () {
            var number = Number($(this).attr('id').trim());
            var json_name = $(this).attr('class');
            file_list.splice(number, 1);
            display_file_list();
            remove_file(json_name);
        });

        // Save a single proof.
        $('div.rbottom').on('click', 'button.save_proof', function () {
            var filename = $(this).attr('theory_name');
            var item_id = $(this).attr('item_id');
            var editor_id = get_selected_id();
            var proof = cells[editor_id].proof;
            var output_proof = [];
            $.each(proof, function (i, prf) {
                output_proof.push($.extend(true, {}, prf));  // perform deep copy
                output_proof[i].th = output_proof[i].th_raw;
                delete output_proof[i].th_raw;
                output_proof[i].args = output_proof[i].args_raw;
                delete output_proof[i].args_raw;
            });
            json_files[filename].content[item_id].proof = output_proof;
            json_files[filename].content[item_id].num_gaps = cells[editor_id].num_gaps;
            if (cur_theory_name === filename) {
                display_theory_items();
            }
            save_json_file(filename);
        });

        // Reset proof to original status.
        $('div.rbottom').on('click', 'button.reset', function () {
            var item_id = $(this).attr('item_id');
            var file_name = $(this).attr('theory_name');
            init_empty_proof(file_name, item_id);
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
                editor.focus();
                resize_editor();
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
            apply_backward_step();
        });

        $('#apply-induction').on("click", function () {
            apply_induction(get_selected_editor());
        });

        $('#rewrite-goal').on("click", function () {
            rewrite_goal();
        });

        // Initialize proof after clicking 'proof' link on the left side.
        $('#panel-content').on('click', 'a[name="proof"]', function (e) {
            e.stopPropagation();
            var item_id = $(this).parents().attr('item_id');
            init_proof_tab(cur_theory_name, item_id);
        });

        // Create editing area after clicking 'edit' link on the left side.
        $('#panel-content').on('click', 'a[name="edit"]', function (e) {
            e.stopPropagation();
            var item_id = $(this).parents().attr('item_id');
            init_edit_area(item_id);
        });

        // Use tab key to insert unicode characters.
        $('#codeTabContent').on('keydown', '.unicode-replace', function (e) {
            var content = $(this).val().trim();
            var id = $(this).attr('id');
            var pos = document.getElementById(id).selectionStart;
            if (pos !== 0 && e.keyCode === 9) {
                var len = '';
                for (var key in replace_obj) {
                    var l = key.length;
                    if (content.substring(pos - l, pos) === key) {
                        if (e && e.preventDefault) {
                            e.preventDefault();
                        } else {
                            window.event.returnValue = false;
                        };
                        len = l;
                        content = content.slice(0, pos - len) + replace_obj[key] + content.slice(pos,);
                    }
                }
                if (len) {
                    $(this).val(content);
                    document.getElementById(id).setSelectionRange(pos - len + 1, pos - len + 1);
                }
            }
        });

        // Auto-adjust number of rows for a textarea.
        $('#codeTabContent').on('input', 'textarea.adjust-rows', function () {
            var rows = $(this).val().split('\n').length;
            $(this).attr('rows', rows);
        });

        // Save information for an item.
        $('div.rbottom').on('click', 'button.save-edit', function () {
            var form = get_selected_edit_form('edit-form');
            var error_id = $(this).next().attr('id');
            var ty = $(this).attr('data_type');
            var theory_name = $(this).attr('theory_name');
            var number = form.number.value;
            var data = {};
            data.file_name = theory_name;
            data.prev_list = json_files[theory_name].content.slice(0, number);
            data.content = make_data(form, ty);
            $.ajax({
                url: '/api/check-modify',
                type: 'POST',
                data: JSON.stringify(data),
                success: function (res) {
                    if ('failed' in res) {
                        $('div#' + error_id).find('pre').text(res.detail_content);
                    } else {
                        if (number === '-1') {
                            json_files[theory_name].content.push(res.content);
                        } else {
                            item = json_files[theory_name].content[number]
                            delete item.hint_forward;
                            delete item.hint_backward;
                            delete item.hint_rewrite;
                            for (var key in res.content) {
                                item[key] = res.content[key];
                            }
                        }
                        save_json_file(theory_name);
                        display_theory_items();
                        alert('Saved ' + item.name);
                    }
                }
            });
        });

        // Select / unselect an item by left click.
        $('#panel-content').on('click','div[name="theories"]',function(){
            var item_id = Number($(this).attr('item_id'));
            if (items_selected.indexOf(item_id) >= 0) {
                var index = items_selected.indexOf(item_id);
                items_selected.splice(index, 1);
            }
            else {
                items_selected.push(item_id);
            }
            items_selected.sort();
            display_theory_items();
        })

        // Delete an item from menu.
        $('div.dropdown-menu.Ctrl a[name="del"]').on('click',function(){
            theory = json_files[cur_theory_name];
            $.each(items_selected, function (i, v) {
                theory.content[v] = '';
            });
            theory.content = theory.content.filter(item => item !== '');
            items_selected = [];
            save_json_file(cur_theory_name);
            display_theory_items();
        })

        // Move up an item or sequence of items.
        $('div.dropdown-menu.Ctrl a[name="up"]').on('click', function() {
            content = json_files[cur_theory_name].content;
            if (items_selected[0] === 0)
                return;
            $.each(items_selected, function (i, v) {
                items_selected[i] = v - 1;
                [content[v-1], content[v]] = [content[v], content[v-1]]
            });
            save_json_file(cur_theory_name);
            display_theory_items();
        })

        // Move down an item or sequence of items.
        $('div.dropdown-menu.Ctrl a[name="down"]').on('click', function(){
            content = json_files[cur_theory_name].content;
            items_selected.reverse();
            if (items_selected[0] === content.length - 1)
                return;
            $.each(items_selected, function (i, v) {
                items_selected[i] = v + 1;
                [content[v], content[v+1]] = [content[v+1], content[v]]
            });
            items_selected.reverse();
            save_json_file(cur_theory_name);
            display_theory_items();
        })

        // Open json file from links in the 'Files' tab.
        $('#panel-files').on('click', 'a[name="file"]', function () {
            open_json_file($(this).text().trim());
        });

        // Open json file from menu.
        $('#json-button').on('click', function () {
            var name = prompt('Please enter the file name');
            if (name !== null) {
                open_json_file(name);
            }
        });

        $('div.dropdown-menu.add-info a').on('click', function () {
            if (selected_tab === 'content') {
                var ty = $(this).attr('name');
                init_edit_area('', ty);
            }
        });

        // On loading page, obtain list of theories.
        $.ajax({
            url: "/api/find-files",
            success: function (res) {
                $('#json-tab-files').click();
                file_list = res.theories;
                display_file_list();
            }
        });
    });

    // Open json file with the given name.
    function open_json_file(name) {
        items_selected = [];
        $('#json-tab-content').click();
        $('#panel-content').empty();
        load_json_file(name);
    }

    // Initialize form for editing metadata.
    function init_metadata_area() {
        page_num++;

        var templ_tab = _.template($("#template-tab").html());
        $('#codeTab').append(templ_tab({page_num: page_num, label: "File"}));

        var templ_form = _.template($('#template-file-metadata').html());
        $('#codeTabContent').append(templ_form({page_num: page_num}));

        var templ_rbottom = _.template($('#template-metadata-rbottom').html());
        $('div.rbottom').append(templ_rbottom({page_num: page_num}));

        $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
        $('div#prf' + page_num).show().siblings().hide();
        $('.code-cell').each(function () {
            $(this).removeClass('active');
        });
    }
    
    // Convert items in the theory from json format for the web client
    // back to the json format for the file.
    function item_to_output(data) {
        if (data.ty === 'def.ax') {
            delete data.type_hl;
        } else if (data.ty === 'thm' || data.ty === 'thm.ax') {
            delete data.prop_hl;
        } else if (data.ty === 'type.ind') {
            delete data.argsT;
            delete data.ext;
        } else if (data.ty === 'def') {
            delete data.type_hl;
            delete data.prop_hl;
        } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
            delete data.type_hl;
            delete data.ext;
            for (var i in data.rules) {
                delete data.rules[i].prop_hl;
            }
        }
    }

    // Save all changed proof on the webpage to the json-file;
    function save_json_file(filename) {
        var content = [];
        $.each(json_files[filename].content, function (i, item) {
            content.push($.extend(true, {}, item));  // perform deep copy
            item_to_output(content[i]);
        });
        var data = {
            name: filename,
            imports: json_files[filename].imports,
            description: json_files[filename].description,
            content: content
        };
        $.ajax({
            url: "/api/save-file",
            type: "POST",
            data: JSON.stringify(data),
        });
    }

    // Initialize edit area, for both editing an existing item and
    // creating a new item.
    // 
    // number: if editing an existing item, id of the current item.
    // data_type: if adding a new item, type of the new item.
    function init_edit_area(number = '', data_type = '') {
        page_num++;

        var data_name = '', data_content = '';
        if (!number) {
            data_name = '', data_content = '';
        } else {
            var item = json_files[cur_theory_name].content[number];
            var data_name = item.name;
            var data_type = item.ty;
        }

        var templ_tab = _.template($("#template-tab").html());
        $('#codeTab').append(templ_tab({page_num: page_num, label: data_type}));

        if (data_type === 'def.ax') {
            if (number)
                data_content = item.type;
            else
                $('#codeTab').find('span#' + page_num).text('constant');
            var templ_edit = _.template($("#template-edit-def-ax").html());
            $('#codeTabContent').append(templ_edit({page_num: page_num}));
            var form = document.getElementById('edit-constant-form' + page_num);
            form.data_name.value = data_name;
            form.data_content.value = data_content;
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            if (number)
                form.number.value = number
            else
                form.number.value = -1
        }
        if (data_type === 'thm' || data_type === 'thm.ax') {
            var templ_edit = _.template($('#template-edit-thm').html());
            $('#codeTabContent').append(templ_edit({page_num: page_num}));

            var form = document.getElementById('edit-thm-form' + page_num);
            if (data_type === 'thm')
                form.name.labels[0].textContent = 'Theorem';
            else
                form.name.labels[0].textContent = 'Axiom';
            if (number) {
                form.number.value = number;
                form.name.value = data_name;
                form.prop.value = item.prop;
                vars_lines = []
                $.each(item.vars, function (nm, T) {
                    vars_lines.push(nm + ' :: ' + T);
                });
                form.vars.rows = vars_lines.length;
                form.vars.value = vars_lines.join('\n');
                if (item.hint_backward === 'true')
                    form.hint_backward.checked = true;
                if (item.hint_forward === 'true')
                    form.hint_forward.checked = true;
                if (item.hint_rewrite === 'true')
                    form.hint_rewrite.checked = true;
            }
            else {
                form.number.value = -1;
            }
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        }
        if (data_type === 'type.ind') {
            if (number) {
                var ext = item.ext;
                var argsT = item.argsT;
                var data_name = item.name;
                var templ_edit = _.template($('#template-edit-type-ind').html());
                $('#codeTabContent').append(templ_edit({
                    page_num: page_num, ext_output: ext.join('\n')
                }));
                var form = document.getElementById('edit-type-form' + page_num);
                $.each(item.constrs, function (i, v) {
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
            data_content = data_content.trim();
            var i = data_content.split('\n').length;
            $('#codeTab').find('span#' + page_num).text(data_name);

            form.data_name.value = data_name;
            form.data_content.textContent = data_content;
            form.data_content.rows = i;
            if (number)
                form.number.value = number
            else
                form.number.value = -1

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
                var vars = '';
                var templ_edit = _.template($('#template-edit-def').html());
                var ext_output = "";
                if ('ext' in item) {
                    ext_output = item.ext.join('\n');
                }
                $('#codeTabContent').append(templ_edit({
                    page_num: page_num, type_name: type_name, ext_output: ext_output
                }));
                var form = document.getElementById('edit-def-form' + page_num);
                data_name = item.name + ' :: ' + item.type;
                if (item.rules) {
                    for (var j in item.rules) {
                        var data_con = '';
                        $.each(item.rules[j].prop_hl, function (i, val) {
                            data_con += val[0];
                        });
                        data_content_list.push(data_con);
                        data_rule_names.push(item.rules[j]['name']);
                    }
                }
                if (data_type === 'def') {
                    var i = 0;
                    data_content_list.push(item.prop);
                    for (v in item.vars) {
                        vars += i + ': ' + v + ':' + item.vars[v] + '\n';
                        i++;
                    }
                }
                for (var i in data_content_list) {
                    data_new_content += i + ': ' + data_content_list[i] + '\n';
                    data_rule_name += i + ': ' + data_rule_names[i] + '\n';
                }
                $('#codeTab').find('span#' + page_num).text(item.name);
            } else
                $('#codeTab').find('span#' + page_num).text('function');
            form.number.value = number;
            form.data_name.value = data_name;
            form.content.textContent = data_new_content.trim();
            form.content.rows = data_new_content.trim().split('\n').length;
            form.data_vars.textContent = vars.trim();
            form.data_vars.rows = vars.trim().split('\n').length;
            if (data_type === 'def.pred') {
                form.vars_names.textContent = data_rule_name.trim();
                form.vars_names.rows = data_rule_name.trim().split('\n').length;
            }
            if (number)
                form.number.value = number
            else
                form.number.value = -1
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');

            if (data_type !== 'def') {
                var data_vars_list = [];
                var data_vars_str = '';
                if (number) {
                    $.each(item.rules, function (i, v) {
                        var vars_str = '';
                        for (let key in v.vars) {
                            vars_str += key + ':' + v.vars[key] + '   ';
                        }
                        data_vars_list.push(vars_str);
                    });
                    $.each(data_vars_list, function (i, v) {
                        data_vars_str += i + ': ' + v + '\n';
                    })
                }
                form.data_vars.value = data_vars_str.trim();
                form.data_vars.rows = form.data_vars.value.split('\n').length;
            }
        }

        var templ_rbottom = _.template($('#template-edit-rbottom').html());
        $('div.rbottom').append(templ_rbottom({
            page_num: page_num, data_type: data_type, theory_name: cur_theory_name}));

        $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
        $('div#prf' + page_num).show().siblings().hide();
    }

    // Read data from the form into item.
    function make_data(form, ty) {
        var item = {};
        if (ty === 'def.ax') {
            item.ty = 'def.ax';
            item.name = form.data_name.value.trim();
            item.type = form.data_content.value.trim();
        }
        if (ty === 'thm' || ty === 'thm.ax') {
            item.ty = ty;
            item.name = form.name.value;
            item.prop = form.prop.value;
            item.vars = {};
            $.each(form.vars.value.split('\n'), function (i, v) {
                let [nm, T] = v.split('::');
                if (nm)
                    item.vars[nm.trim()] = T.trim();
            });
            if (form.hint_backward.checked === true)
                item.hint_backward = 'true';
            if (form.hint_forward.checked ===  true)
                item.hint_forward = 'true';
            if (form.hint_rewrite.checked ===  true)
                item.hint_rewrite = 'true';
        }
        if (ty === 'type.ind') {
            var data_name = form.data_name.value.trim();
            var data_content = form.data_content.value.trim();
            var temp_list = [], temp_constrs = [];
            var temp_content_list = data_content.split(/\n/);
            if (data_name.split(/\s/).length > 1) {
                temp_list.push(data_name.split(/\s/)[0].slice(1,));
                item.name = data_name.split(/\s/)[1];
            } else {
                item.name = data_name;
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
                    type = item.name;
                }
                temp_con_dict['type'] = type;
                temp_con_dict['args'] = args;
                temp_con_dict['name'] = arg_name;
                temp_constrs.push(temp_con_dict);
            });
            item.ty = 'type.ind';
            item.args = temp_list;
            item.constrs = temp_constrs;
        }
        if (ty === 'def.ind' || ty === 'def' || ty === 'def.pred') {
            var data_name = form.data_name.value.trim();
            var data_content = form.content.value.trim();
            var rules_list = [];
            var props_list = data_content.split(/\n/);
            var vars_list = form.data_vars.value.trim().split(/\n/);
            if (ty === 'def.pred')
                var names_list = form.vars_names.value.trim().split(/\n/);
            $.each(vars_list, function (i, m) {
                vars_list[i] = m.slice(3,).trim();
            });
            $.each(props_list, function (i, v) {
                props_list[i] = v.slice(3,).trim();
                if (names_list)
                    names_list[i] = names_list[i].slice(3,).trim();
            });
            $.each(props_list, function (i, v) {
                temp_dict = {}
                temp_vars = {};
                if (ty !== 'def' && v && vars_list[i]) {
                    temp_dict['prop'] = v;
                    $.each(vars_list[i].split(/\s\s\s/), function (j, k) {
                        temp_vars[k.split(':')[0].trim()] = k.split(':')[1].trim();
                    });
                    if (names_list)
                        temp_dict['name'] = names_list[i];
                } else if (!v) {
                    return true;
                }
                temp_dict['vars'] = temp_vars;
                rules_list.push(temp_dict);
                item.rules = rules_list;
            });
            if (ty === 'def') {
                var temp_vars_ = {};
                $.each(vars_list, function (j, k) {
                    temp_vars_[$.trim(k.split(':')[0])] = $.trim(k.split(':')[1]);
                });
                item.prop = $.trim(props_list[0]);
                item.vars = temp_vars_;
            }
            item.ty = ty;
            item.name = data_name.split(' :: ')[0];
            item.type = data_name.split(' :: ')[1];
        }
        return item;
    }

    // Add new tab for editing proofs
    function init_proof_tab(theory_name, item_id) {
        page_num++;
        // Add new tab
        var templ_tab = _.template($("#template-tab").html());
        $('#codeTab').append(templ_tab({page_num: page_num, label: ""}));

        // Add CodeMirror textarea
        var templ_codepan = _.template($("#template-codepan").html());
        $('#codeTabContent').append(templ_codepan({page_num: page_num}));

        // Add buttons and location for displaying results
        var templ_rbottom = _.template($("#template-proof-rbottom").html());
        $('div.rbottom').append(templ_rbottom({
            page_num: page_num, item_id: item_id, theory_name: theory_name
        }));

        init_editor("code" + page_num, theory_name);

        $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
        $('div#prf' + page_num).show().siblings().hide();
        $('.code-cell').each(function () {
            $(this).removeClass('active');
        });

        var cur_item = json_files[theory_name].content[item_id];
        var thm_name = cur_item.name;

        $('#codeTab li[name="code' + page_num + '"] span').text(thm_name);
        if (cur_item.proof)
            init_saved_proof(theory_name, item_id);
        else
            init_empty_proof(theory_name, item_id);
    }

    function display_file_list() {
        $(function () {
            $('#panel-files').html('');
            var templ = _.template($("#template-file-list").html());
            $('#panel-files').append(templ({file_list: file_list}));    
        });
    }

    function remove_file(file_name) {
        $.ajax({
            url: '/api/remove-file',
            data: JSON.stringify(file_name),
            type: 'PUT',
            success: function () {
                alert('Removed file ' + file_name);
            }
        })
    }

    // Initialize empty proof for the theorem with given file name and item_id.
    function init_empty_proof(file_name, item_id) {
        var item = json_files[file_name].content[item_id];
        var data = {
            'id': get_selected_id(),
            'vars': item.vars,
            'prop': item.prop,
            'theory_name': file_name,
            'thm_name': item.name
        };
        display_running();
        $.ajax({
            url: "/api/init-empty-proof",
            type: "POST",
            data: JSON.stringify(data),
            success: function (result) {
                display_checked_proof(result, 0);
                display_instructions(item.instructions);
            }
        });
    }

    // Load saved proof for the theorem with given file name and item_id.
    function init_saved_proof(file_name, item_id) {
        var item = json_files[file_name].content[item_id];
        var data = {
            'id': get_selected_id(),
            'vars': item.vars,
            'proof': item.proof,
            'theory_name': file_name,
            'thm_name': item.name
        };
        display_running();
        $.ajax({
            url: "/api/init-saved-proof",
            type: 'POST',
            data: JSON.stringify(data),
            success: function (result) {
                display_checked_proof(result, 0);
                display_instructions(item.instructions);
            }
        })
    }

    // Display items for the current theory on the left side of the page.
    function display_theory_items() {
        var theory = json_files[cur_theory_name];
        var templ = _.template($("#template-content-theory_desc").html());
        $('#panel-content').html(templ({
            theory_desc: theory.description,
            import_str: theory.imports.join(' ')
        }));
        $.each(theory.content, function(num, ext) {
            var class_item = 'theory_item';
            if (items_selected.indexOf(num) >= 0) {
                class_item = 'theory_item selected_item';
            }
            var templ = _.template($("#template-content-" + ext.ty.replace(".", "-")).html());
            $('#panel-content').append(templ({
                num: num, ext: ext, class_item: class_item
            }));
        });
    }

    // Load json file from server and display the results.
    function load_json_file(name) {
        cur_theory_name = name;
        if (name in json_files) {
            display_theory_items();
        } else {
            $.ajax({
                url: "/api/load-json-file",
                type: "POST",
                data: JSON.stringify(name),
                success: function (result) {
                    json_files[cur_theory_name] = result.data;
                    display_theory_items();
                }
            });
        }
    }   

    function init_editor(id, theory_name) {
        var editor = CodeMirror.fromTextArea(document.getElementById(id), {
            mode: "text/x-python",
            lineNumbers: true,
            firstLineNumber: 0,
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
        editor.setValue("");
        $(editor.getTextArea().parentNode).addClass('selected').siblings().removeClass('selected');
        resize_editor();

        cells[id] = {
            theory_name: theory_name,
            facts: new Set(),
            goal: -1,
            edit_line_number: -1,
        };
        editor.on("keydown", function (cm, event) {
            let line_no = cm.getCursor().line;
            let line = cm.getLine(line_no);
            if (event.code === 'Enter') {
                event.preventDefault();
                if (cells[id].edit_line_number !== -1) {
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
                if (cells[id].edit_line_number !== -1) {
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
                    cells[id].edit_line_number = -1;
                }
            }
        });

        editor.on("focus", function (cm) {
            $(cm.getTextArea().parentNode).addClass('selected').siblings().removeClass('selected');
        });

        editor.on("cursorActivity", function (cm) {
            if (is_mousedown) {
                mark_text(cm);
                match_thm();
                is_mousedown = false;
            }
        });

        editor.on('beforeChange', function (cm, change) {
            if (!edit_flag &&
                cells[get_selected_id()].edit_line_number !== change.from.line) {
                change.cancel();
            }
        });

        editor.on('mousedown', function (cm, event) {
            var timer = 0;
            is_mousedown = true;
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
            cm.addSelection({line: line_num, ch: ch - 5}, {line: line_num, ch: ch});
            cells[id].edit_line_number = line_num;
        } else if (line.trim() === '') {
            cells[id].edit_line_number = line_num;
        }
    }

    function mark_text(cm) {
        var line_num = cm.getCursor().line;
        var line = cm.getLineHandle(line_num).text;
        var id = get_selected_id();
        if (line.indexOf('sorry') !== -1) {
            // Choose a new goal
            cells[id].goal = line_num;
        }
        else if (cells[id].goal !== -1) {
            // Choose or unchoose a fact
            if (cells[id].facts.has(line_num))
                cells[id].facts.delete(line_num)
            else
                cells[id].facts.add(line_num)
        }
        display_facts_and_goal(cm);
    }

    function resize_editor() {
        editor = document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
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
