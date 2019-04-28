var edit_flag = false;
var is_mousedown = false;
var cells = {};

function get_selected_id() {
    return document.querySelector('.code-cell.selected textarea').id;
}

function get_selected_editor() {
    return document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
}

function get_selected_output() {
    return document.querySelector('.rbottom .selected .output pre');
}

function get_selected_instruction() {
    return document.querySelector('.rbottom .selected .output #instruction');
}

function get_selected_instruction_number() {
    return document.querySelector('.rbottom .selected .output #instruction-number');
}

function get_selected_edit_form(name) {
    return document.querySelector('.code-cell.active form[name=' + name + ']');
}

function display_running() {
    var status_output = get_selected_output();
    status_output.innerHTML = "Running";
}

// Display proof returned from the server.
//
// result: proof data returned from the server.
// pre_line_no: line number for the sorry before the operation.
function display_checked_proof(result, pre_line_no) {
    var status_output = get_selected_output();
    var id = get_selected_id();

    if ("failed" in result) {
        status_output.innerHTML = result["failed"] + ": " + result["message"];
        status_output.style.color = 'red';
    } else {
        cells[id].edit_line_number = -1;
        cells[id]['proof'] = result['proof'];
        var editor = get_selected_editor();
        editor.startOperation();
        edit_flag = true;
        display(id);
        edit_flag = false;
        editor.endOperation();
        var num_gaps = result["report"]["num_gaps"];
        cells[id]['num_gaps'] = num_gaps;
        status_output.style.color = '';
        if (num_gaps > 0) {
            status_output.innerHTML = "OK. " + num_gaps + " gap(s) remaining."
        } else {
            status_output.innerHTML = "OK. Proof complete!"
        }

        var line_count = editor.lineCount();
        var new_line_no = -1;
        for (var i = pre_line_no; i < line_count; i++) {
            if (editor.getLine(i).indexOf('sorry') !== -1) {
                new_line_no = i;
                break
            }
        }
        if (new_line_no === -1) {
            editor.setCursor(0, 0);
            cells[id].facts.clear();
            cells[id].goal = -1;
        } else {
            editor.setCursor(new_line_no, 0);
            cells[id].facts.clear();
            cells[id].goal = new_line_no;    
        }
        display_facts_and_goal(editor);
        match_thm();
        editor.focus();
    }
}

function display_instructions(instructions) {
    var instr_output = get_selected_instruction();
    instr_output.innerHTML = instructions[0];
    var instr_no_output = get_selected_instruction_number();
    instr_no_output.innerHTML = '1/' + instructions.length;
}

function add_line_after(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_no = cm.getCursor().line;
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_no]['id'],
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/add-line-after",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result, line_no);
                cm.setCursor(line_number + 1, Number.MAX_SAFE_INTEGER);
            }
        })
    })
}

function remove_line(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_no = cm.getCursor().line;
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_no]['id'],
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/remove-line",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result, line_no);
                cm.setCursor(line_no - 1, Number.MAX_SAFE_INTEGER);
            }
        })
    })
}

function introduction(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_no = cm.getCursor().line;
        var line = cm.getLine(line_no);
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_no]['id'],
            "var_name": ""
        };

        if (line.indexOf("have ∀") !== -1 || line.indexOf("show ∀") !== -1) {
            input["var_name"] = prompt('Enter variable name').split(",")
        }
        var data = JSON.stringify(input);
        display_running();
        $.ajax({
            url: "/api/introduction",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result, line_no);
            }
        })
    })
}

function apply_induction(cm) {
    $(document).ready(function () {
        var line_no = cm.getCursor().line;
        var id = get_selected_id();
        var input = {
            'id': id,
            'line_id': cells[id]['proof'][line_no]['id']
        };

        input['theorem'] = prompt('Enter induction theorem and variable name');
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/apply-induction",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result, line_no);
            }
        })
    })
}

// Split off the first token according to the delimiter.
function split_one(s, delimiter) {
    arr = s.split(delimiter);
    return [arr[0], arr.slice(1).join(delimiter)];
}

// Produce proof item from id and user-input string.
function split_line(id, s) {
    var item = {};
    item.id = id
    if (s.indexOf(" by ") > 0) {
        rest = split_one(s, " by ")[1];
    } else {
        rest = s.trim()
    }
    item.th = "";

    if (rest.indexOf(" ") >= 0)
        [item.rule, rest] = split_one(rest, ' ');  // split off name of rule
    else
        [item.rule, rest] = rest, "";
    item.rule = item.rule.trim();

    if (rest.indexOf("from") >= 0) {
        [item.args, item.prevs] = split_one(rest, 'from');
        item.args = item.args.trim();
        item.prevs = item.prevs.split(',');
        return item;
    } else {
        item.args = rest.trim();
        item.prevs = [];
        return item;
    }
}

function set_line(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_no = cells[id].edit_line_number;
        var input = {
            'id': get_selected_id(),
            'item': split_line(cells[id].proof[line_no].id, cm.getLine(line_no))
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/set-line",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result, line_no);
            }
        })
    })
}

// Query the server to match theorems for each parameterized tactic
function match_thm() {
    var id = get_selected_id();
    var goal = cells[id].goal;
    var facts = cells[id].facts;

    if (goal === -1) {
        return;
    }

    var facts_id = [];
    facts.forEach(val => {
        facts_id.push(cells[id]['proof'][val]['id']);
    });
    var data = {
        'id': id,
        'goal_id': cells[id]['proof'][goal]['id'],
        'facts_id': facts_id,
        'theory_name': cells[id].theory_name
    };
    $.ajax({
        url: "/api/match-thm",
        type: "POST",
        data: JSON.stringify(data),
        success: function (result) {
            var templ_variable = _.template($('#template-variable').html());
            $('div#variable').html(templ_variable({ctxt: result.ctxt}));

            cells[id]['match_thm'] = result;
            display_match_thm(result);
        }
    });
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
// p[0] is the printed stpython -m pip install --upgrade pipring, p[1] is the color.
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
        return true
    }
    var line_id = cells[id]['proof'][line_no].id
    var line_id2 = cells[id]['proof'][line_no + 1].id
    return line_id.split('.').length > line_id2.split('.').length
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
        ch = display_highlight_strs(editor, line.args, line_no, ch);
    } else if (line.rule === 'variable') {
        ch = display_str(editor, 'fix ', line_no, ch, {css: 'color: darkcyan; font-weight: bold'});
        ch = display_highlight_strs(editor, line.args, line_no, ch);
    } else if (line.rule === 'subproof') {
        ch = display_have_prompt(editor, id, line_no, ch);
        ch = display_highlight_strs(editor, line.th, line_no, ch);
        ch = display_str(editor, ' with', line_no, ch, {css: 'color: darkblue; font-weight: bold'});
    } else {
        // Display theorem with highlight
        if (line.th.length > 0) {
            ch = display_have_prompt(editor, id, line_no, ch);
            ch = display_highlight_strs(editor, line.th, line_no, ch);
            ch = display_str(editor, ' by ', line_no, ch, {css: 'font-weight: bold'});
        }
        // Display rule name
        ch = display_str(editor, line.rule, line_no, ch);
        // Display args with highlight
        if (line.args.length > 0) {
            ch = display_str(editor, ' ', line_no, ch);
            ch = display_highlight_strs(editor, line.args, line_no, ch);
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
    var proof = cells[id]['proof'];
    editor.setOption('lineNumberFormatter', function (line_no) {
        if (line_no < proof.length) {
            return proof[line_no].id;
        } else {
            return '';
        }
    });
    var large_num = 0;
    $.each(proof, function (line_no, line) {
        var id_len = line.id.length;
        if (id_len >= large_num)
            large_num = id_len;
        display_line(id, line_no);
        var len = editor.getLineHandle(line_no).text.length;
        editor.replaceRange('\n', {line: line_no, ch: len}, {line: line_no, ch: len + 1});
    });
    $('div.code-cell.selected div.CodeMirror-gutters').css('width', 32 + large_num * 3 + 'px');
    $('div.CodeMirror-gutters').css('text-align', 'left');
    $('div.code-cell.selected div.CodeMirror-sizer').css('margin-left', 32 + large_num * 3 + 'px');
}

function display_match_thm(result) {
    $('div.rbottom .selected .match-thm').html('');
    var template_match_thm = _.template($("#template-match-thm").html());

    $.each(tactic_info, function (key) {
        if (result[key].length !== 0) {
            $('div.rbottom .selected .match-thm').append(template_match_thm({
                func_name: key,
                result: result[key],
            }));    
        }
    });
    $('div.rbottom .selected .match-thm').append('<div class=clear></div>')
}

// Apply proof step parameterized by theorems.
// select_thm: index of selected theorem, -1 for apply other theorem.
function apply_thm_tactic(select_thm = -1, func_name = '') {
    let api = tactic_info[func_name].api;
    if (api === undefined)
        return;

    let id = get_selected_id();
    let match_thm_list = cells[id]['match_thm'][func_name];
    let facts = cells[id].facts;
    let line_no = cells[id].goal;

    if (line_no === -1)
        return;

    if (match_thm_list.length === 0)
        select_thm = -1

    // Obtain the list of fact_id separated by commas.
    facts_id = []
    facts.forEach(function (val) {
        facts_id.push(cells[id]['proof'][val]['id']);
    });
    fact_id = facts_id.join(', ');
    goal_id = cells[id]['proof'][line_no]['id']

    if (select_thm !== -1) {
        var theorem = match_thm_list[select_thm][0];
        if (fact_id !== "") {
            theorem += ', ' + fact_id;
        }
        var data = {
            'id': id,
            'line_id': goal_id,
            'theorem': theorem,
        };
        $.ajax({
            url: api,
            type: "POST",
            data: JSON.stringify(data),
            success: function (result) {
                display_checked_proof(result, line_no);
            }
        });
    } else {
        var title = 'Goal: ' + goal_id
        if (facts.size !== 0) {
            title = title + '\nFacts: ' + fact_id;
        }
        swal({
            title: title,
            html: '<input id="swal-input1" class="swal2-input">',
            showCancelButton: true,
            confirmButtonText: 'confirm',
            showLoaderOnConfirm: true,
            focusConfirm: false,
            allowOutsideClick: () => !swal.isLoading(),
            preConfirm: () => {
                document.querySelector('#swal-input1').focus();
                var theorem = document.getElementById('swal-input1').value;
                if (facts.size !== 0) {
                    theorem = theorem + ', ' + fact_id;
                }
                var data = {
                    'id': id,
                    'line_id': goal_id,
                    'theorem': theorem,
                };
                return $.ajax({
                    url: api,
                    type: "POST",
                    data: JSON.stringify(data),
                    success: function (result) {
                        if ('failed' in result)
                            swal.showValidationMessage('Request failed: ' + result['failed'])
                        else
                            return result
                    }
                });
            }
        }).then((result) => {
            if (result) {
                display_checked_proof(result.value, line_no);
            }
        })
    }
}

function apply_backward_step() {
    apply_thm_tactic(0, 'backward')
}

function apply_forward_step() {
    apply_thm_tactic(0, 'forward');
}

function rewrite_goal() {
    apply_thm_tactic(0, 'rewrite');
}