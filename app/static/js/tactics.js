var edit_flag = false;
var cells = {};

function get_selected_id() {
    return document.querySelector('.code-cell.selected textarea').id;
}

function get_selected_editor() {
    return document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
}

function get_selected_edit_form(name) {
    return document.querySelector('.code-cell.active form[name=' + name + ']');
}

function display_status(status, color='') {
    var status_output = document.querySelector('.rbottom .selected .output pre');
    status_output.innerHTML = status;
    status_output.style.color = color;
}

function display_running() {
    display_status('Running');
}

// Display proof returned from the server.
function display_checked_proof(result) {
    var id = get_selected_id();

    if ("failed" in result) {
        display_status(result.failed + ": " + result.message, 'red');
    } else {
        cells[id].proof = result.proof;
        var editor = get_selected_editor();
        editor.startOperation();
        edit_flag = true;
        display(id);
        edit_flag = false;
        editor.endOperation();
        var num_gaps = result.report.num_gaps;
        cells[id].num_gaps = num_gaps;
        if (num_gaps > 0) {
            display_status("OK. " + num_gaps + " gap(s) remaining.");
        } else {
            display_status("OK. Proof complete!");
        }

        if ('goal' in result) {
            // Looking at a previous step, already has goal_id and fact_id
            cells[id].goal = result.goal;
            cells[id].facts = [];
            if ('facts' in result) {
                cells[id].facts = result.facts;
            }
        } else {
            var line_count = editor.lineCount();
            var new_line_no = -1;
            var pre_line_no = 0;
            if (cells[id].goal !== -1)
                pre_line_no = cells[id].goal;
            for (var i = pre_line_no; i < line_count; i++) {
                if (editor.getLine(i).indexOf('sorry') !== -1) {
                    new_line_no = i;
                    break
                }
            }
            if (new_line_no === -1) {
                editor.setCursor(0, 0);
                cells[id].facts = [];
                cells[id].goal = -1;
            } else {
                editor.setCursor(new_line_no, 0);
                cells[id].facts = [];
                cells[id].goal = new_line_no;    
            }    
        }
        display_facts_and_goal(editor);
        match_thm();
        editor.focus();
    }
}

function get_line_no_from_id(id, proof) {
    var found = -1;
    $.each(proof, function (i, v) {
        if (v.id === id)
            found = i;
    });
    return found;
}

function display_instructions() {
    var id = get_selected_id();
    var instr_output = document.querySelector('.rbottom .selected .output #instruction');
    var instr_no_output = document.querySelector('.rbottom .selected .output #instruction-number');
    var h_id = cells[id].index;
    instr_output.innerHTML = highlight_html(cells[id].history[h_id].steps_output);
    instr_no_output.innerHTML = h_id + '/' + (cells[id].history.length-1);
    var proof_info = {
        proof: cells[id].history[h_id].proof,
        report: cells[id].history[h_id].report
    };
    if (h_id < cells[id].steps.length) {
        // Find line number corresponding to ids
        proof_info.goal = get_line_no_from_id(cells[id].steps[h_id].goal_id, proof_info.proof);
        proof_info.facts = [];
        if (cells[id].steps[h_id].fact_ids !== undefined) {
            cells[id].steps[h_id].fact_ids.forEach(
                v => proof_info.facts.push(get_line_no_from_id(v, proof_info.proof))
            );
        }
    }
    display_checked_proof(proof_info);
}

// Obtain the current state of proof
function current_state() {
    var id = get_selected_id();
    var goal_no = cells[id].goal;
    if (goal_no === -1)
        return undefined;

    var fact_ids = [];
    cells[id].facts.forEach(v => fact_ids.push(cells[id].proof[v].id));
    return {
        'id': id,
        'goal_id': cells[id].proof[goal_no].id,
        'fact_ids': fact_ids,
        'theory_name': cells[id].theory_name,
        'thm_name': cells[id].thm_name,
        'vars': cells[id].vars,
        'proof': cells[id].proof
    }
}

// Make ajax call to apply-method with the given input.
// On success, record the step and display the updated proof.
function apply_method_ajax(input) {
    $.ajax({
        url: "/api/apply-method",
        type: "POST",
        data: JSON.stringify(input),
        success: function(result) {
            if ("query" in result) {
                // Query for more parameters
                result.query.forEach(param => input[param] = prompt(param));
                apply_method_ajax(input);
            } else {
                // Success
                var id = input.id;
                var h_id = cells[id].index;
                cells[id].steps[h_id] = input;
                cells[id].steps.length = h_id+1;
                cells[id].history[h_id+1] = {
                    'steps_output': [['current_state', 0]],
                    'proof': result.proof,
                    'report': result.report
                };
                cells[id].history.length = h_id+2;
                delete input.id;
                if (input.fact_ids.length == 0)
                    delete input.fact_ids;
                delete input.theory_name;
                delete input.thm_name;
                delete input.vars;
                delete input.proof;
                cells[id].index += 1;
                display_instructions();
            }
        }
    })
}

// Apply method with the given name and initial set of arguments
function apply_method(method_name, args) {
    var count = 0;
    var sig_list = [];
    var id = get_selected_id();
    var sigs = cells[id].method_sig[method_name];
    var input = current_state();
    input.method_name = method_name;
    if (args === undefined)
        args = {};
    $.each(sigs, function (i, sig) {
        if (sig in args)
            input[sig] = args[sig];
        else {
            sig_list.push(sig);
            count += 1;
        }
    });
    display_running();

    if (count > 0) {
        var input_html = '';
        for (let i = 1; i <= count; i++) {
            input_html += '<label style="text-align:right;width:15%">' + sig_list[i-1] +
                          ':</label>&nbsp;<input id="sig-input' + i + '" style="width:70%;"><br>';
        }
        swal({
            title: "Method " + method_name,
            html: input_html,
            showCancelButton: true,
            confirmButtonText: "Confirm",
            cancelButtonText: "Cancel",
            preConfirm: () => {
                for (let i = 1; i <= count; i++) {
                    input[sig_list[i-1]] = document.getElementById('sig-input' + i).value;
                }
            }
        }).then(function (isConfirm) {
            if (isConfirm.value) {
                apply_method_ajax(input);
            }
        });
    } else {
        apply_method_ajax(input);
    }
}

// Query the server to match theorems for each parameterized tactic
function match_thm() {
    var id = get_selected_id();
    var input = current_state();
    if (input === undefined) {
        cells[id].search_res = [];
        display_match_thm();
    }
    else {
        $.ajax({
            url: "/api/search-method",
            type: "POST",
            data: JSON.stringify(input),
            success: function (result) {
                var templ_variable = _.template($('#template-variable').html());
                $('div#panel-proof').html(templ_variable({ctxt: result.ctxt}));
    
                cells[id].search_res = result.search_res;
                display_match_thm();
            }
        });    
    }
}

// Print string without highlight at given line_no and ch. Return the new value of ch.
function display_str(editor, str, line_no, ch, mark) {
    len = str.length;
    editor.replaceRange(str, {line: line_no, ch: ch}, {line: line_no, ch: ch + len});
    if (typeof mark !== 'undefined') {
        editor.markText({line: line_no, ch: ch}, {line: line_no, ch: ch + len}, mark);
    }
    return ch + len;
}

// Print string with highlight at given line_no and ch.
// p[0] is the printed string, p[1] is the color.
// Return the new value of ch.
function display_highlight_str(editor, p, line_no, ch) {
    var color;
    if (p[1] === 0)
        color = "color: black";
    else if (p[1] === 1)
        color = "color: green";
    else if (p[1] === 2)
        color = "color: blue";
    else if (p[1] === 3)
        color = "color: purple";
    else if (p[1] === 4)
        color = "color: silver";
    return display_str(editor, p[0], line_no, ch, {css: color});
}

// Display a list of pairs with highlight
function display_highlight_strs(editor, ps, line_no, ch) {
    $.each(ps, function (i, p) {
        ch = display_highlight_str(editor, p, line_no, ch);
    })
    return ch;
}

// Detect whether the given line is the last of a section
function is_last_id(id, line_no) {
    if (cells[id]['proof'].length - 1 === line_no) {
        return true;
    }
    return cells[id]['proof'][line_no+1].rule === 'intros';
}

function display_have_prompt(editor, id, line_no, ch) {
    if (is_last_id(id, line_no)) {
        return display_str(editor, 'show ', line_no, ch, {css: 'color: darkcyan; font-weight: bold'});
    } else {
        return display_str(editor, 'have ', line_no, ch, {css: 'color: darkblue; font-weight: bold'});
    }
}

// Print a single line.
function display_line(id, line_no) {
    var editor = get_selected_editor();
    var line = cells[id]['proof'][line_no];
    var ch = 0;

    // Display id in bold
    var str_temp = ''
    for (var i = 0; i < line.id.length; i++) {
        if (line.id[i] === '.') {
            str_temp += '  '
        }
    }
    ch = display_str(editor, str_temp, line_no, ch, {css: 'font-weight: bold'});

    if (line.rule === 'assume') {
        ch = display_str(editor, 'assume ', line_no, ch, {css: 'color: darkcyan; font-weight: bold'});
        ch = display_highlight_strs(editor, line.args_hl, line_no, ch);
    } else if (line.rule === 'variable') {
        ch = display_str(editor, 'fix ', line_no, ch, {css: 'color: darkcyan; font-weight: bold'});
        ch = display_highlight_strs(editor, line.args_hl, line_no, ch);
    } else if (line.rule === 'subproof') {
        ch = display_have_prompt(editor, id, line_no, ch);
        ch = display_highlight_strs(editor, line.th_hl, line_no, ch);
        ch = display_str(editor, ' with', line_no, ch, {css: 'color: darkblue; font-weight: bold'});
    } else {
        // Display theorem with highlight
        if (line.th_hl.length > 0) {
            ch = display_have_prompt(editor, id, line_no, ch);
            ch = display_highlight_strs(editor, line.th_hl, line_no, ch);
            ch = display_str(editor, ' by ', line_no, ch, {css: 'font-weight: bold'});
        }
        // Display rule name
        ch = display_str(editor, line.rule, line_no, ch);
        // Display args with highlight
        if (line.args_hl.length > 0) {
            ch = display_str(editor, ' ', line_no, ch);
            ch = display_highlight_strs(editor, line.args_hl, line_no, ch);
        }
        if (line.prevs.length > 0) {
            ch = display_str(editor, ' from ', line_no, ch, {css: 'font-weight: bold'});
            ch = display_str(editor, line.prevs.join(', '), line_no, ch);
        }
    }
    get_selected_editor().execCommand("goDocEnd");
}

// Display the given content in the textarea with the given id.
function display(id) {
    var editor = get_selected_editor();
    editor.setValue('');
    var proof = cells[id].proof;
    editor.setOption('lineNumberFormatter', function (line_no) {
        if (line_no < proof.length) {
            return proof[line_no].id;
        } else {
            return '';
        }
    });
    var max_id_len = 0;
    $.each(proof, function (line_no, line) {
        var id_len = line.id.length;
        if (id_len >= max_id_len)
        max_id_len = id_len;
        display_line(id, line_no);
        var len = editor.getLineHandle(line_no).text.length;
        editor.replaceRange('\n', {line: line_no, ch: len}, {line: line_no, ch: len + 1});
        if (line.rule === 'intros') {
            editor.markText({line: line_no, ch: 0}, {line: line_no}, {inclusiveRight: true, inclusiveLeft: true, collapsed: 'true'});
        }
    });
    $('div.code-cell.selected div.CodeMirror-gutters').css('width', 32 + max_id_len * 3 + 'px');
    $('div.CodeMirror-gutters').css('text-align', 'left');
    $('div.code-cell.selected div.CodeMirror-sizer').css('margin-left', 32 + max_id_len * 3 + 'px');
}

function display_match_thm() {
    var id = get_selected_id();
    var search_res = cells[id].search_res;

    $('div.rbottom .selected .match-thm').html('');
    var template_match_thm = _.template($("#template-match-thm").html());

    $('div.rbottom .selected .match-thm').append(template_match_thm({search_res}));
    $('div.rbottom .selected .match-thm').append('<div class=clear></div>');
}

function apply_thm_tactic(res_id) {
    var id = get_selected_id();
    var res = cells[id].search_res[res_id];
    if (res === undefined)
        return;

    apply_method(res._method_name, res);
}
