(function ($) {
    var selected_tab = 'files';   // Selected tab on the left side.
    var page_num = 0;   // Number of tabs opened on the right side.
    var cur_theory_name = "";  // Name of the current theory file.
    var json_files = {};  // All loaded theory data.
    var file_list = [];  // List of all files for the current user.
    var items_selected = [];  // List of selected items in the displayed theory.

    // Used to distinguish between click and drag
    var drag = false;
    var startingPos = [0, 0];

    var is_mousedown = false;  // Used to manage mouse click.

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
            if (cell.index < cell.history.length-1) {
                cell.index++;
                display_instructions();
            }
        });

        // Add new json file.
        $('#new-file').click(init_metadata_area);

        $('button#additional-option-items,#additional-option-file,#additional-option-action').click(() => {
            if ($('div.rtop').css('z-index') !== '-100')
                $('div.rtop').css('z-index', '-100');
        })

        $('div#right,div.dropdown-menu>a').click(()=> {
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
            var json_content = json_files[filename].content[item_id];
            if (cells[editor_id].steps.length === 0) {
                // Empty proof
                delete json_content.proof;
                delete json_content.num_gaps;
                delete json_content.steps;
            } else {
                if (cells[editor_id].history !== undefined) {
                    var len = cells[editor_id].history.length;
                    var proof = cells[editor_id].history[len-1].proof;
                    json_content.num_gaps = cells[editor_id].history[len-1].report.num_gaps;
                } else {
                    var proof = cells[editor_id].proof;
                    json_content.num_gaps = cells[editor_id].num_gaps;
                }
                var output_proof = [];
                $.each(proof, function (i, prf) {
                    output_proof.push($.extend(true, {}, prf));  // perform deep copy
                    delete output_proof[i].th_hl;
                    delete output_proof[i].args_hl;
                });
                json_content.proof = output_proof;
                json_content.steps = cells[editor_id].steps;
            }
            if (cur_theory_name === filename) {
                // Refresh status of item if the current theory is being displayed
                display_theory_items();
            }
            save_json_file(filename);
            alert('Saved ' + json_content.name + '.');
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

        $('#undo-move').on("click", function () {
            undo_move();
        });

        $('#introduction').on("click", function () {
            apply_method('introduction');
        });

        $('#new-var').on("click", function () {
            apply_method('new_var');
        });

        $('#apply-cut').on("click", function () {
            apply_method('cut');
        });

        $('#apply-cases').on("click", function () {
            apply_method('cases');
        });

        $('#apply-backward-step').on("click", function () {
            apply_method('apply_backward_step');
        });

        $('#apply-forward-step').on("click", function () {
            apply_method('apply_forward_step');
        });

        $('#apply-induction').on("click", function () {
            apply_method('induction');
        });

        $('#rewrite-goal').on("click", function () {
            apply_method('rewrite_goal');
        });

        $('#rewrite-fact').on("click", function () {
            apply_method('rewrite_fact');
        });

        // Initialize proof after clicking 'proof' link on the left side.
        $('#panel-content').on('mousedown', 'a[name="proof"]', function (e) {
            e.stopPropagation();
            var item_id = $(this).parents().attr('item_id');
            init_proof_tab(cur_theory_name, item_id);
        });

        // Create editing area after clicking 'edit' link.
        $('a#edit_item').click(function() {
            if (items_selected.length === 1) {
                init_edit_area(items_selected[0]);
            }
        });

        $('a#add_before, a#add_after, a#add_end').click(function() {
            var num = 0;
            if (cur_theory_name && items_selected.length === 1) {
                if ($(this).attr('id') === 'add_before') {
                    json_files[cur_theory_name].content.splice(items_selected[0], 0, {'ty': 'pre-data'});
                    num = items_selected[0];
                    items_selected[0] += 1;
                }
                else if($(this).attr('id') === 'add_after') {
                    var item_id = items_selected[0];
                    json_files[cur_theory_name].content.splice(item_id+1, 0, {'ty':'pre-data'});
                    num = item_id + 1;
                }
            }
            if (cur_theory_name && $(this).attr('id') === 'add_end') {
                json_files[cur_theory_name].content.push({'ty':'pre-data'});
                num = json_files[cur_theory_name].content.length - 1;
            }
            display_theory_items();
            init_edit_area(num);
            save_json_file(cur_theory_name);
        })

        // Use tab key to insert unicode characters.
        $(document).on('keydown', '.unicode-replace', function (e) {
            var content = $(this).val().trim();
            var pos = this.selectionStart;
            if (pos !== 0 && e.keyCode === 13) {  // Enter
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
                    this.setSelectionRange(pos - len + 1, pos - len + 1);
                }
            }
        });

        $('#codeTabContent').on('input', '.form-element', function () {
            adjust_input_size(this);
        });

        // Save information for an item.
        $('div.rbottom').on('click', 'button.save-edit', function () {
            var form = get_selected_edit_form('edit-form');
            var error_id = $(this).next().attr('id');
            var theory_name = form.info.theory_name;
            var number = form.info.number;
            var data = {};
            data.file_name = theory_name;
            data.prev_list = json_files[theory_name].content.slice(0, Number(number));
            data.content = make_data(form);
            $.ajax({
                url: '/api/check-modify',
                type: 'POST',
                data: JSON.stringify(data),
                success: function (res) {
                    if ('failed' in res) {
                        $('div#' + error_id).find('pre').text(res.detail_content);
                    } else {
                        delete res.content.data_content;
                        delete res.content.data_name;
                        item = json_files[theory_name].content[number];
                        $.extend(true, item, res.content);

                        save_json_file(theory_name);
                        display_theory_items();
                        alert('Saved ' + item.name);
                    }
                }
            });
        });

        $('#panel-content').on('mousedown', 'div[name="theories"]', function (e) {
            drag = false;
            startingPos = [e.pageX, e.pageY];
            if (e.shiftKey) {
                e.preventDefault();
            }
        });

        $('#panel-content').on('mousemove', 'div[name="theories"]', function (e) {
            if (!(e.pageX === startingPos[0] && e.pageY === startingPos[1])) {
                drag = true;
            }
        });

        // Select / unselect an item by left click.
        $('#panel-content').on('mouseup','div[name="theories"]', function (e) {
            if (!drag) {
                var item_id = Number($(this).attr('item_id'));
                if (e.shiftKey) {
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
            }
        });

        function add_selected_items(id1, id2) {
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

        // Delete an item from menu.
        $('div.dropdown-menu a#delete_item').on('click',function() {
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
            } else if (e.keyCode === 65 && e.ctrlKey) {  // Ctrl+A
                e.preventDefault();
                $('a#add_after').click();
            } else if (e.keyCode === 66 && e.ctrlKey) {  // Ctrl+B
                e.preventDefault();
                $('a#add_before').click();
            } else if (e.keyCode === 68 && e.ctrlKey) {  // Ctrl+D
                e.preventDefault();
                $('a#delete_item').click();
            } else if (e.keyCode === 69 && e.ctrlKey) {  // Ctrl+E
                e.preventDefault();
                $('a#edit_item').click();
            } else if (e.keyCode === 90 && e.ctrlKey) {  // Ctrl+Z
                e.preventDefault();
                undo_move();
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

        // Show appropriate form content on changing type of item.
        $('div.code-pan').on('change', 'select', function () {
            var page_n = $(this).attr('name');
            var ty = $(this).find('option:selected').val();
            $('div.total' + page_n).each(function() {
                if ($(this).attr('class').indexOf('hidden-ele') < 0) {
                    $(this).addClass('hidden-ele');
                }
                if (ty === 'def.ax')
                    $('div[name="constant-' + page_n + '"]').removeClass('hidden-ele');
                if (ty === 'thm' || ty === 'thm.ax')
                    $('div[name="thm-' + page_n + '"]').removeClass('hidden-ele');
                if (ty === 'type.ind')
                    $('div[name="type-' + page_n + '"]').removeClass('hidden-ele');
                if (ty === 'def' || ty === 'def.ind' || ty === 'def.pred')
                    $('div[name="def-' + page_n + '"]').removeClass('hidden-ele');
            })
            $('div.rbottom button#' + page_n).attr('data_type', ty);
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

    // Auto-adjust size of input and textarea.
    function adjust_input_size(input) {
        var text = $(input).val();
        var test_width = $(input).closest('form').find('pre.test-width');
        test_width.text(text);
        var min_width = $(input).attr('min-width');
        $(input).css('width', test_width.css('width'));
        if (min_width !== undefined && $(input).width() < Number(min_width)) {
            $(input).css('width', min_width + 'px');
        }
        $(input).attr('rows', text.split('\n').length);
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
        } else if (data.ty === 'def.ind' || data.ty === 'def.pred') {
            delete data.type_hl;
            delete data.ext;
            delete data.edit_content;
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

    // Initialize area for editing an item.
    // 
    // number: id of the item being edited. This may be a new item
    // (indicated by item.ty = 'pre-data') or an existing item.
    function init_edit_area(number) {
        page_num++;

        // Get item to be edited, determine whether it is new item
        // from its type.
        var item = json_files[cur_theory_name].content[number];
        var data_type = item.ty;
        var new_data = false;
        var tab_name = item.name;
        if (data_type == 'pre-data') {
            data_type = 'thm';
            new_data = true;
            tab_name = "(new item)";
        }

        // Add tab
        var templ_tab = _.template($("#template-tab").html());
        $('#codeTab').append(templ_tab({page_num: page_num, label: tab_name}));

        // Add edit form
        var templ_edit = _.template($("#template-edit-thm").html());
        $('#codeTabContent').append(templ_edit({page_num: page_num}));
        var form = document.getElementById('edit-thm-form' + page_num);
        $('select#dropdown_datatype' + page_num).val(data_type);

        form.info = {};
        form.info.data_type = data_type;
        form.info.theory_name = cur_theory_name;
        form.info.number = number;

        if (data_type === 'def.ax') {
            form.const_name.value = item.name;
            form.const_type.value = item.type;
            adjust_input_size(document.getElementById('const-name' + page_num));
            adjust_input_size(document.getElementById('const-type' + page_num));
            $('span#const-head' + page_num).removeClass('hidden-ele');
        }

        if (data_type === 'thm' || data_type === 'thm.ax') {
            if (data_type === 'thm')
                $('label#thm-label'+ page_num).text('theorem');
            else
                $('label#thm-label'+ page_num).text('axiom');
            if (!new_data) {
                form.name.value = item.name;
                form.prop.value = item.prop;
                form.vars.value = item.vars_lines.join('\n');
                if (item.attributes && item.attributes.includes('hint_backward'))
                    form.hint_backward.checked = true;
                if (item.attributes && item.attributes.includes('hint_backward1'))
                    form.hint_backward1.checked = true;
                if (item.attributes && item.attributes.includes('hint_forward'))
                    form.hint_forward.checked = true;
                if (item.attributes && item.attributes.includes('hint_rewrite'))
                    form.hint_rewrite.checked = true;
                if (item.attributes && item.attributes.includes('hint_resolve'))
                    form.hint_resolve.checked = true;
            }
            adjust_input_size(document.getElementById('thm-name' + page_num));
            adjust_input_size(document.getElementById('thm-vars' + page_num));
            adjust_input_size(document.getElementById('thm-prop' + page_num));
            $('span#thm-head' + page_num).removeClass('hidden-ele');
            $('div#thm'+ page_num).removeClass('hidden-ele');
        }

        if (data_type === 'type.ind') {
            form.type_edit_name.value = item.edit_type;
            form.type_constrs.textContent = item.constr_output.join('\n');
            adjust_input_size(document.getElementById('type-edit-name' + page_num));
            adjust_input_size(document.getElementById('type-constrs' + page_num));

            $('pre#type-ext'+ page_num).html(item.ext_output);
            $('span#type-head' + page_num).removeClass('hidden-ele');
            $('div#type'+ page_num).removeClass('hidden-ele');
        }

        if (data_type === 'def.ind' || data_type === 'def.pred' || data_type === 'def') {
            if (data_type === 'def')
                $('label#def-label' + page_num).text('definition');
            else if (data_type == 'def.pred')
                $('label#def-label' + page_num).text('inductive');
            else
                $('label#def-label' + page_num).text('fun');

            form.def_name.value = item.name;
            form.def_type.value = item.type;
            adjust_input_size(document.getElementById('def-name' + page_num));
            adjust_input_size(document.getElementById('def-type' + page_num));
            
            if (data_type == 'def' && 'overload' in item) {
                form.overload = item.overload;
            }
            if (data_type === 'def') {
                form.def_content.textContent = item.edit_content;
                if (item.attributes && item.attributes.includes('hint_rewrite'))
                    form.hint_rewrite_def.checked = true;
            } else {
                form.def_content.textContent = item.edit_content.join('\n');
                $('pre#def-ext'+ page_num).html(item.ext_output);
            }
            adjust_input_size(document.getElementById('def-content' + page_num));

            $('span#def-head' + page_num).removeClass('hidden-ele');
            $('div#def' + page_num).removeClass('hidden-ele');
        }

        // Display type of item as label or dropdown box depending on new_data.
        if (new_data)
            $('div.data-title'+ page_num).hide();
        else
            $('select#dropdown-datatype'+ page_num).hide();

        // Add SAVE button.
        var templ_rbottom = _.template($('#template-edit-rbottom').html());
        $('div.rbottom').append(templ_rbottom({page_num: page_num}));

        // Adjust visibility and selected tabs.
        $('#codeTab a[href="#code' + page_num + '-pan"]').tab('show');
        $('div#prf' + page_num).addClass('selected').siblings().removeClass('selected');
        $('div#prf' + page_num).show().siblings().hide();
    }

    // Read data from the form into item.
    function make_data(form) {
        var item = {};
        var ty = form.info.data_type;
        item.ty = ty;
        if (ty === 'def.ax') {
            item.name = form.const_name.value.trim();
            item.type = form.const_type.value.trim();
        }
        if (ty === 'thm' || ty === 'thm.ax') {
            item.name = form.name.value;
            item.prop = form.prop.value;
            item.vars = form.vars.value.trim().split('\n');
            item.attributes = [];
            if (form.hint_backward.checked === true)
                item.attributes.push('hint_backward');
            if (form.hint_backward1.checked === true)
                item.attributes.push('hint_backward1');
            if (form.hint_forward.checked === true)
                item.attributes.push('hint_forward');
            if (form.hint_rewrite.checked === true)
                item.attributes.push('hint_rewrite');
            if (form.hint_resolve.checked === true)
                item.attributes.push('hint_resolve');
        }
        if (ty === 'type.ind') {
            item.data_name = form.type_edit_name.value.trim();
            item.data_content = form.type_constrs.value.trim().split('\n');
        }
        if (ty === 'def.ind' || ty === 'def' || ty === 'def.pred') {
            item.name = form.def_name.value.trim();
            item.type = form.def_type.value.trim();
            if (ty === 'def')
                item.prop = form.def_content.value.trim();
                item.attributes = [];
                if (form.hint_rewrite_def.checked == true)
                    item.attributes.push('hint_rewrite');
                if ('overload' in form)
                    item.overload = form.overload;
            else
                item.data_content = form.def_content.value.trim().split('\n');
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
            setTimeout(function () {
                var templ = _.template($("#template-file-list").html());
                $('#panel-files').html(templ({file_list: file_list})); 
            }, 100)   
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
                cells[id].vars = result.vars;
                cells[id].thm_name = item.name;
                cells[id].steps = [];
                cells[id].history = [{
                    'steps_output': [['Current state', 0]],
                    'proof': result.proof,
                    'report': result.report
                }];
                cells[id].index = 0;
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
            'prop': item.prop,
            'proof': item.proof,
            'theory_name': file_name,
            'thm_name': item.name,
            'steps': item.steps
        };
        display_running();
        $.ajax({
            url: "/api/init-saved-proof",
            type: 'POST',
            data: JSON.stringify(data),
            success: function (result) {
                if ("failed" in result) {
                    display_status(result.failed + ": " + result.message, 'red');
                } else {
                    var id = get_selected_id();
                    cells[id].goal = -1;
                    cells[id].method_sig = result.method_sig;
                    cells[id].vars = result.vars;
                    cells[id].thm_name = item.name;
                    cells[id].steps = result.steps;
                    if (result.history !== undefined) {
                        cells[id].history = result.history;
                        cells[id].index = result.history.length-1;
                        display_instructions();
                    } else {
                        display_checked_proof(result);
                    }
                }
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
                "Ctrl-I": function () {
                    apply_method('introduction')
                },
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
        resize_editor();

        cells[id] = {
            theory_name: theory_name,
            facts: new Set(),
            goal: -1
        };

        editor.on("focus", function (cm) {
            $(cm.getTextArea().parentNode).addClass('selected').siblings().removeClass('selected');
        });

        editor.on('beforeChange', function (cm, change) {
            if (!edit_flag) {
                change.cancel();
            }
        });

        editor.on('cursorActivity', function (cm) {
            if (is_mousedown) {
                mark_text(cm);
                match_thm();
                is_mousedown = false;
            }
        });

        editor.on('mousedown', function (cm) {
            is_mousedown = true;
        });
    }

    // Select goal or fact
    function mark_text(cm) {
        var line_num = cm.getCursor().line;
        var line = cm.getLineHandle(line_num).text;
        var id = get_selected_id();
        if (line_num >= cells[id].proof.length) {
            return;
        }
        if (line.indexOf('sorry') !== -1) {
            // Choose a new goal
            cells[id].goal = line_num;
        }
        else if (cells[id].goal !== -1) {
            // Choose or unchoose a fact
            i = cells[id].facts.indexOf(line_num);
            if (i === -1)
                cells[id].facts.push(line_num);
            else
                cells[id].facts.splice(i, 1);
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
