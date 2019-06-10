(function ($) {
    var selected_tab = 'files';   // Selected tab on the left side.
    var page_num = 0;   // Number of tabs opened on the right side.
    var cur_theory_name = "";  // Name of the current theory file.
    var json_files = {};  // All loaded theory data.
    var file_list = [];  // List of all files for the current user.
    var items_selected = [];  // List of selected items in the displayed theory.
    var click_count = 0;
    var add_tab_number = ''; //add new data tab's page_num;

    $(function () {
        document.getElementById('left').style.height = (window.innerHeight - 40) + 'px';

        // Load html templates
        var includes = $('[data-include]');
        jQuery.each(includes, function () {
            var file = "../" + $(this).data('include') + '.html';
            $(this).load(file);
        });

        $('#right').on('click', '.thm-content pre', function () {
            apply_thm_tactic($(this).index());
        });

        $('#right').on('click', '#link-backward', function () {
            var cell = cells[get_selected_id()];
            if (cell.index > 0) {
                cell.index--;
                display_instructions();
            }
        });

        $('#right').on('click', '#link-forward', function () {
            var cell = cells[get_selected_id()];
            if (cell.index < cell.instructions.length - 1) {
                cell.index++;
                display_instructions();
            }
        });

        // Add new json file.
        $('#new-file').click(init_metadata_area);

        $('button#additional-option-items,#additional-option-file,#additional-option-action').click(() => {
            $('div.rtop').css('z-index', '-100');
        })

        $('div#right').click(()=> {
            if ($('div.rtop').css('z-index') === '-100')
                $('div.rtop').css('z-index', '0');
        })

        // Refresh file data.
        $('#refresh-files').click(function () {
            $.ajax({
                url: '/api/refresh-files',
                type: 'POST',
                data: JSON.stringify({}),
                success: function() {
                    location.reload();
                }
            })
        });

        // Save metadata for json file.
        $('div.rbottom').on('click', 'button[name="save-metadata"]', function () {
            var form = get_selected_edit_form('edit-form');
            var prev_name = form.prev_name.value;
            var fname = form.fname.value.trim();
            if (form.imports.value.trim() == '')
                var imports = []
            else
                var imports = form.imports.value.split(',');
            var description = form.description.value.trim();

            if (prev_name === '') {
                file_list.push(fname);
                file_list.sort();
                display_file_list();
                json_files[fname] = {
                    name: fname,
                    imports: imports,
                    description: description,
                    content: []
                }
            } else {
                json_files[fname].imports = imports;
                json_files[fname].description = description;
            }
            save_json_file(fname);
            alert('Saved ' + fname);
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
            var filename = file_list[number];

            init_metadata_area();
            var form = document.getElementById('edit-metadata-form' + page_num);
            if (filename in json_files) {
                data = json_files[filename];
                form.prev_name.value = data.name;
                form.fname.value = data.name;
                form.imports.value = data.imports.join(',');
                form.description.textContent = data.description;
                form.description.rows = 5;
            } else {
                $.ajax({
                    url: '/api/load-json-file',
                    data: JSON.stringify(filename),
                    type: 'POST',
                    success: function (res) {
                        json_files[res.name] = res
                        form.prev_name.value = res.name;
                        form.fname.value = res.name;
                        form.imports.value = res.imports.join(',');
                        form.description.textContent = res.description;
                        form.description.rows = 5;
                    }
                })    
            }
        });

        $('div#panel-files').on('click', 'a[name="delete"]', function () {
            var number = Number($(this).attr('id').slice(6,).trim());
            var filename = file_list[number];
            file_list.splice(number, 1);
            remove_file(filename);
            display_file_list();
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
            alert('Saved ' + json_files[filename].content[item_id].name + '.');
        });

        // Reset proof to original status.
        $('div.rbottom').on('click', 'button.reset', function () {
            var item_id = $(this).attr('item_id');
            var file_name = $(this).attr('theory_name');
            init_empty_proof(file_name, item_id);
        });

        // Click a tab to show.
        $('#codeTab').on("click", "a", function (e) {
            e.preventDefault();
            var tab_pm = $(this).attr('name');
            $(this).tab('show');
            $('div#prf' + tab_pm).addClass('selected').siblings().removeClass('selected');
            $('div#prf' + tab_pm).show().siblings().hide();
        });

        // Set cursor & size.
        $('#codeTab').on('shown.bs.tab', 'a', function () {
            if (document.querySelector('.code-cell.active textarea + .CodeMirror')) {
                var editor = document.querySelector('.code-cell.active textarea + .CodeMirror').CodeMirror;
                editor.focus();
                resize_editor();
            }
        });

        // Delete a tab.
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

        $('#introduction').on("click", introduction);

        $('#new-var').on("click", function () {
            apply_method('new_var')
        });

        $('#apply-cases').on("click", function () {
            apply_method('cases')
        });

        $('#apply-forall-elim').on("click", function () {
            apply_method('forall_elim')
        });

        $('#rewrite-goal-with-prev').on("click", function () {
            apply_method('rewrite_goal_with_prev')
        });

        $('#apply-prev').on('click', function () {
            apply_method('apply_prev')
        });

        $('#add-line-after').on("click", function () {
            add_line_after(get_selected_editor());
        });

        $('#apply-backward-step').on("click", function () {
            apply_method('apply_backward_step')
        });

        $('#apply-induction').on("click", function () {
            apply_method('induction')
        });

        $('#rewrite-goal').on("click", function () {
            apply_method('rewrite_goal')
        });

        // Initialize proof after clicking 'proof' link on the left side.
        $('#panel-content').on('click', 'a[name="proof"]', function (e) {
            e.stopPropagation();
            var item_id = $(this).parents().attr('item_id');
            init_proof_tab(cur_theory_name, item_id);
        });

        // Create editing area after clicking 'edit' link.
        $('a#edit_item').click(function() {
            if (items_selected.length === 1) {
                var item_id = items_selected[0];
                init_edit_area(String(item_id));
            }
        });

        $('a#add_before, a#add_after, a#add_end').click(function() {
            init_edit_area('', 'thm', add_mode = true);
            if (cur_theory_name && items_selected.length === 1) {
                if ($(this).attr('id') === 'add_before') {
                    json_files[cur_theory_name].content.splice(items_selected[0], 0, {'ty': 'pre-data'});
                    items_selected[0] += 1;
                }
                else if($(this).attr('id') === 'add_after') {
                    var item_id = items_selected[0];
                    json_files[cur_theory_name].content.splice(item_id+1, 0, {'ty':'pre-data'});
                }
            }
            if (cur_theory_name && $(this).attr('id') === 'add_end') {
                    json_files[cur_theory_name].content.push({'ty':'pre-data'});
                }
            display_theory_items();
            save_json_file(cur_theory_name);
        })

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
            if (ty === 'def.ax')
                var data_type = 'constant';
            else if (ty === 'thm' || ty === 'thm.ax')
                var data_type = 'thm';
            else if (ty === 'type.ind')
                var data_type = 'type';
            else
                var data_type = 'def';
            var theory_name = $(this).attr('theory_name');
            var number = form['number-'+ data_type].value;
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
                        item = res.content;
                        delete item.data_content;
                        delete item.names_list;
                        delete item.data_name;
                        if (number === '' || number === '-1') {
//                            json_files[theory_name].content.push(item);
                            $.each(json_files[theory_name].content, function(i, j) {
                                if (j['ty'] === 'pre-data') {
                                    json_files[theory_name].content[i] = item;
                                }
                            })
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
        $('#panel-content').on('click','div[name="theories"]', function (e) {
            var item_id = Number($(this).attr('item_id'));
            if(e.shiftKey) {
                preventD(e);
                add_selected_items(item_id, items_selected[items_selected.length - 1]);
                display_theory_items();
            }
            else {
                if (items_selected.indexOf(item_id) >= 0) {
                    items_selected.length = 0;
                }
                else {
                    items_selected.length = 0;
                    items_selected.push(item_id);
                }
                items_selected.sort();
                display_theory_items();
            }
        })

        function add_selected_items (id1, id2) {
            if (id1 > id2) {
                for (let i = id2; i <= id1; i++) {
                    if (items_selected.indexOf(i) === -1)
                        items_selected.push(i);
                }
                items_selected.sort();
            }
            else if (id1 < id2) {
                for (let i = id1; i <= id2; i++) {
                    if (items_selected.indexOf(i) === -1)
                        items_selected.push(i);
                }
                items_selected.sort();
            }
        }

        function preventD (e) {
            if (e && e.preventDefault) {
                e.preventDefault();
            }
            else {
                window.event.returnValue = false;
            };
        }

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
        function item_exchange_up() {
            $.each(items_selected, function (i, v) {
                items_selected[i] = v - 1;
                [content[v-1], content[v]] = [content[v], content[v-1]]
            });
        }

        $(document).keydown(function (e) {
            if (e.keyCode === 38 && e.ctrlKey) {
                content = json_files[cur_theory_name].content;
                if (items_selected[0] === 0)
                    return;
                if ($('div[item_id="0"]').attr('name') && items_selected[0] !== 0) {
                    item_exchange_up();
                }
                else if (items_selected[0] !== 1) {
                    item_exchange_up();
                }
                save_json_file(cur_theory_name);
                display_theory_items();
            }
        })

        // Move down an item or sequence of items.
        $(document).keydown(function (e) {
            if (e.ctrlKey && e.keyCode === 40 &&
                items_selected[items_selected.length-1] < json_files[cur_theory_name].content.length-1) {
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
            }
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

        // Add new item from menu.
        $('button#additional_option_additem').on('click', function () {
            if (selected_tab === 'content') {
                var ty = 'thm';
                init_edit_area('', ty);
            }
        });

        $('div.code-pan').on('change' ,'select', function() {
            var page_n = $(this).attr('name');
            var ty = $(this).find('option:selected').val();
            $('div.total'+ page_n).each(function() {
                if ($(this).attr('class').indexOf('hidden-ele') < 0) {
                    $(this).addClass('hidden-ele');
                }
            if (ty === 'def.ax')
                $('div[name="constant-'+ page_n+ '"]').removeClass('hidden-ele');
            if (ty === 'thm' || ty === 'thm.ax')
                $('div[name="thm-'+ page_n+ '"]').removeClass('hidden-ele');
            if (ty === 'type.ind')
                $('div[name="type-'+page_n+'"]').removeClass('hidden-ele');
            if (ty === 'def' || ty === 'def.ind' || ty === 'def.pred')
                $('div[name="def-'+page_n+'"]').removeClass('hidden-ele');
            })
            $('div.rbottom button#'+ page_n).attr('data_type', ty);
        })

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

        cur_theory_name = name;
        if (name in json_files) {
            display_theory_items();
        } else {
            $.ajax({
                url: "/api/load-json-file",
                type: "POST",
                data: JSON.stringify(name),
                success: function (result) {
                    json_files[cur_theory_name] = result;
                    display_theory_items();
                }
            });
        }
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
            delete data.vars_lines;
        } else if (data.ty === 'type.ind') {
            delete data.constr_output;
            delete data.constr_output_hl;
            delete data.type_hl;
            delete data.edit_type;
            delete data.ext_output;
        } else if (data.ty === 'def') {
            delete data.type_hl;
            delete data.prop_hl;
            delete data.edit_content;
            delete data.type_name;
        } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
            delete data.type_hl;
            delete data.ext;
            delete data.edit_content;
            delete data.type_name;
            delete data.ext_output;
            for (var i in data.rules) {
                delete data.rules[i].prop_hl;
            }
        }
    }

    // Save all changed proof on the webpage to the json-file;
    function save_json_file(filename) {
        var content = [];
        $.each(json_files[filename].content, function (i, item) {
            content.push($.extend(true, {}, item));  // perform deep copy//////
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
    function init_edit_area(number = '', data_type = '', add_mode = false) {
        page_num++;
        var ext_output = '';
        var templ_tab = _.template($("#template-tab").html());
        if (number) {
            var item = json_files[cur_theory_name].content[number];
            var data_type = item.ty;
        }
        $('#codeTab').append(templ_tab({page_num: page_num, label: data_type}));
        if (data_type === 'def.ax') {
            var templ_edit = _.template($("#template-edit-thm").html());
            $('#codeTabContent').append(templ_edit({page_num: page_num, ext_output: ext_output, type_name: ''}));
            var form = document.getElementById('edit-thm-form' + page_num);
            if (!number) {
                form['number-constant'].value = -1;
            }
            else {
                form.data_name.value = item['name'];
                form.data_content_constant.value = item['type'];
                form['number-constant'].value = number;
            }
            $('div[name="constant-' + page_num +'"]').removeClass('hidden-ele');
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        }

        if (data_type === 'thm' || data_type === 'thm.ax') {
            if (add_mode) {
                add_tab_number = page_num;
                $('ul#codeTab li[name="code'+ page_num +'"] a').text('New-data');
            }
            var templ_edit = _.template($('#template-edit-thm').html());
            $('#codeTabContent').append(templ_edit({page_num: page_num, ext_output: ext_output, type_name: ''}));
            var form = document.getElementById('edit-thm-form' + page_num);
            if (data_type === 'thm')
                $('label#thm--'+ page_num).text('Theorem');
            else
                $('label#thm--'+ page_num).text('Axiom');
            if (number) {
                form['number-thm'].value = number;
                form.name.value = item['name'];
                form.prop.value = item['prop'];
                vars_lines = item['vars_lines']
                form.vars.rows = vars_lines.length;
                form.vars.value = vars_lines.join('\n');
                if (item['hint_backward'] === 'true')
                    form.hint_backward.checked = true;
                if (item['hint_forward'] === 'true')
                    form.hint_forward.checked = true;
                if (item['hint_rewrite'] === 'true')
                    form.hint_rewrite.checked = true;
            }
            else {
                form['number-thm'].value = -1;
            }
            $('div[name="thm-'+ page_num +'"]').removeClass('hidden-ele');
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        }

        if (data_type === 'type.ind') {
            var templ_edit = _.template($('#template-edit-thm').html());

            if (number) {
                $('#codeTabContent').append(templ_edit({
                    page_num: page_num, ext_output: item.ext_output, type_name: ''
                }));
                $('#codeTab').find('span#' + page_num).text(item.name);

                var form = document.getElementById('edit-thm-form' + page_num);
                form.data_name_type.value = item.edit_type;
                form.data_content_type.textContent = item.constr_output.join('\n');
                form.data_content_type.rows = item.constr_output.length;
                form['number-type'].value = number
            } else {
                $('#codeTab').find('span#' + page_num).text('datatype');

                var form = document.getElementById('edit-thm-form' + page_num);
                form['number-type'].value = -1;
            }
            $('div[name="type-'+ page_num +'"]').removeClass('hidden-ele');
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        }

        if (data_type === 'def.ind' || data_type === 'def.pred' || data_type === 'def') {
            var templ_edit = _.template($('#template-edit-thm').html());
            if (number) {
                $('#codeTabContent').append(templ_edit({
                    page_num: page_num, ext_output: item.ext_output, type_name: item.type_name
                }));
                $('#codeTab').find('span#' + page_num).text(item.name);

                var form = document.getElementById('edit-thm-form' + page_num);
                if (data_type === 'def') {
                    form.content.textContent = item.edit_content;
                    form.content.rows = 1;
                } else {
                    form.content.textContent = item.edit_content.join('\n');
                    form.content.rows = item.edit_content.length;    
                }
                form['number-def'].value = number;
                form.data_name_def.value = item.name + ' :: ' + item.type;
            } else {
                init_editor("data-content" + page_num, cur_theory_name, content = '', flag=false);
                form['number-def'].value = -1;
                $('#codeTab').find('span#' + page_num).text('function');
            }
            $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
            $('div[name="def-'+ page_num +'"]').removeClass('hidden-ele');
        }
        if (number)
            $('div.dropdown-box'+ page_num).hide();
        else
            $('div.data-title'+ page_num).hide();
        var templ_rbottom = _.template($('#template-edit-rbottom').html());
        $('div.rbottom').append(templ_rbottom({
            page_num: page_num, data_type: data_type, theory_name: cur_theory_name}));
        $('select#dropdown_datatype' + page_num).val(data_type);
        $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
        $('div#prf' + page_num).show().siblings().hide();
    }

    // Read data from the form into item.
    function make_data(form, ty) {
        var item = {};
        if (ty === 'def.ax') {
            item.ty = 'def.ax';
            item.name = form.data_name.value.trim();
            item.type = form.data_content_constant.value.trim();
        }
        if (ty === 'thm' || ty === 'thm.ax') {
            item.ty = ty;
            item.name = form.name.value;
            item.prop = form.prop.value;
            item.vars = form.vars.value.trim().split('\n');
            if (form.hint_backward.checked === true)
                item.hint_backward = 'true';
            if (form.hint_forward.checked === true)
                item.hint_forward = 'true';
            if (form.hint_rewrite.checked === true)
                item.hint_rewrite = 'true';
        }
        if (ty === 'type.ind') {
            item.data_name = form.data_name_type.value.trim();
            item.data_content = form.data_content_type.value.trim().split('\n');
            item.ty = 'type.ind';
        }
        if (ty === 'def.ind' || ty === 'def' || ty === 'def.pred') {
            item.ty = ty;
            item.name = form.data_name_def.value.split('::')[0].trim();
            item.type = form.data_name_def.value.split('::')[1].trim();
            if (ty === 'def')
                item.prop = form.content.value.trim();
            else
                item.data_content = form.content.value.trim().split('\n');
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

    // Display list of files.
    function display_file_list() {
        $(function () {
            var templ = _.template($("#template-file-list").html());
            $('#panel-files').html(templ({file_list: file_list}));    
        });
    }

    // Remove given file from directory.
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
                var id = get_selected_id();
                cells[id].goal = -1;
                cells[id].method_sig = result.method_sig;
                display_checked_proof(result);
                cells[id].instructions = item.instructions;
                cells[id].index = 0;
                if (cells[id].instructions !== undefined)
                    display_instructions();
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
                var id = get_selected_id();
                cells[id].goal = -1;
                cells[id].method_sig = result.method_sig;
                display_checked_proof(result);
                cells[id].instructions = item.instructions;
                cells[id].index = 0;
                if (cells[id].instructions !== undefined)
                    display_instructions();
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

    function init_editor(id, theory_name, content='', flag=true) {
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
                "Ctrl-B": function () {
                    apply_method('apply_backward_step')
                },
                "Ctrl-R": function () {
                    apply_method('rewrite_goal')
                },
                "Ctrl-F": function () {
                    apply_method('apply_forward_step')
                },
                "Ctrl-Q": function (cm) {
                    cm.foldCode(cm.getCursor());
                }
            }
        });
        editor.setValue('');
        $(editor.getTextArea().parentNode).addClass('selected').siblings().removeClass('selected');
        if (flag)
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
