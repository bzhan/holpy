var edit_flag = false;

var cells = {};

// Mode for displaying proof
// 显示证明的模式
// 0 - 显示所有内容。 1 - 只显示id和thm。
var mod = 0;

function get_selected_id() {
    return document.querySelector('.code-cell.selected textarea').id;
}

function get_selected_editor() {
    return document.querySelector('.code-cell.selected textarea + .CodeMirror').CodeMirror;
}

function get_selected_output() {
    return document.querySelector('.code-cell.selected .output pre');
}

function get_selected_instruction() {
    return document.querySelector('.code-cell.selected .output #instruction');
}

function get_selected_instruction_number() {
    return document.querySelector('.code-cell.selected .output #instruction-number');
}

function clear_match_thm() {
    $('.match-thm').empty();
}

function display_running() {
    var status_output = get_selected_output();
    status_output.innerHTML = "Running";
}

// Display result returned from the server.
function display_checked_proof(result) {
    var status_output = get_selected_output();

    if ("failed" in result) {
        status_output.innerHTML = result["failed"] + ": " + result["message"];
        status_output.style.color = 'red';
    } else {
        edit_flag = true;
        let id = get_selected_id();
        cells[id].edit_line_number = -1;
        cells[id]['proof'] = result['proof'];
        display(id);
        var num_gaps = result["report"]["num_gaps"];
        cells[id]['num_gaps'] = num_gaps;
        status_output.style.color = '';
        if (num_gaps > 0) {
            status_output.innerHTML = "OK. " + num_gaps + " gap(s) remaining."
        } else {
            status_output.innerHTML = "OK. Proof complete!"
        }
    }
}

function display_instuctions(instructions) {
    var instr_output = get_selected_instruction();
    instr_output.innerHTML = instructions[0];
    var instr_no_output = get_selected_instruction_number();
    instr_no_output.innerHTML = '1/' + instructions.length;
}

function add_line_after(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_number = cm.getCursor().line;
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_number]['id'],
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/add-line-after",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result);
                cm.setCursor(line_number + 1, Number.MAX_SAFE_INTEGER);
            }
        })
    })
}

function remove_line(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_number = cm.getCursor().line;
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_number]['id'],
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/remove-line",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result);
                cm.setCursor(line_number - 1, Number.MAX_SAFE_INTEGER);
            }
        })
    })
}

function introduction(cm) {
    $(document).ready(function () {
        var id = get_selected_id();
        var line_number = cm.getCursor().line;
        var line = cm.getLine(line_number);
        var input = {
            "id": id,
            "line_id": cells[id]['proof'][line_number]['id'],
        };

        if (line.indexOf("⊢ ∀") !== -1) {
            input["var_name"] = prompt('Enter variable name').split(",")
        }
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/introduction",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result);
                cm.setCursor(line_number + result['line-diff'], Number.MAX_SAFE_INTEGER);
            }
        })
    })
}

function apply_backward_step(cm, is_others = false, select_thm = -1) {
    var match_thm_list = get_match_thm();
    var title = '';
    var id = get_selected_id();
    var click_line_number = cells[id].click_line_number;
    var ctrl_click_line_numbers = cells[id].ctrl_click_line_numbers;
    if (is_others)
        match_thm_list.length = 0;
    if (match_thm_list.length !== 0) {
        let idx = select_thm !== -1 ? select_thm : 0;
        let fact_id = '';
        let theorem = '';
        if (click_line_number !== -1 && ctrl_click_line_numbers.size !== 0) {
            ctrl_click_line_numbers.forEach((val) => {
                    fact_id += '' + cells[get_selected_id()]['proof'][val]['id'] + ', ';
            });
        }
        fact_id = fact_id.slice(0, fact_id.length - 2);
        theorem = match_thm_list[idx] + ', ' + fact_id;
        var data = {
            'id': get_selected_id(),
            'line_id': cells[get_selected_id()]['proof'][click_line_number]['id'],
            'theorem': theorem,
        };
        $.ajax({
            url: "/api/apply-backward-step",
            type: "POST",
            data: JSON.stringify(data),
            success: function (result) {
                cells[id].click_line_number = -1;
                cells[id].ctrl_click_line_numbers.clear();
                clear_match_thm();
                display_checked_proof(result);
            }
        });
    } else {
        if (click_line_number !== -1 && ctrl_click_line_numbers.size !== 0) {
            let conclusion = '';
            ctrl_click_line_numbers.forEach((val) => {
                    conclusion += '' + (val + 1) + ', ';
            });
            conclusion = conclusion.slice(0, conclusion.length - 2);
            title = 'Target: ' + (click_line_number + 1) + '\nConclusion: ' + conclusion;
        } else if (click_line_number !== -1 && ctrl_click_line_numbers.size === 0) {
            title = 'Target: ' + (click_line_number + 1);
        } else {
            title = 'Please enter the theorem used';
        }
        swal({
            title: title,
            html:
                '<input id="swal-input1" class="swal2-input">',
            showCancelButton: true,
            confirmButtonText: 'confirm',
            showLoaderOnConfirm: true,
            focusConfirm: false,
            preConfirm: () => {
                document.querySelector('#swal-input1').focus();
                let fact_id = '';
                let theorem = '';
                if (click_line_number !== -1 && ctrl_click_line_numbers.size !== 0) {
                    ctrl_click_line_numbers.forEach((val) => {
                        fact_id += '' + cells[get_selected_id()]['proof'][val]['id'] + ', ';
                    });
                    fact_id = fact_id.slice(0, fact_id.length - 2);
                    theorem = document.getElementById('swal-input1').value + ', ' + id;
                } else if (click_line_number !== -1 && ctrl_click_line_numbers.size === 0) {
                    theorem = document.getElementById('swal-input1').value;
                }
                var data = {
                    'id': get_selected_id(),
                    'line_id': cells[get_selected_id()]['proof'][click_line_number]['id'],
                    'theorem': theorem,
                };
                return fetch('/api/apply-backward-step', {
                        method: 'POST', // or 'PUT'
                        body: JSON.stringify(data),
                        headers: {
                            headers: {
                                'Accept': 'application/json',
                                'Content-Type': 'application/json',
                            },
                        },
                    }
                ).then(response => {
                    if (!response.ok) {
                        throw new Error(response.statusText)
                    }
                    return response.json()
                })
                    .catch(error => {
                        swal.showValidationMessage(
                            `Request failed: ${error}`
                        )
                    })
            },
            allowOutsideClick:
                () => !swal.isLoading()
        }).then((result) => {
            if (result) {
                cells[id].click_line_number = -1;
                cells[id].ctrl_click_line_numbers.clear();
                clear_match_thm();
                display_checked_proof(result['value']);
            }
        })
    }
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
                display_checked_proof(result);
            }
        })
    })
}

function rewrite_goal(cm) {
    $(document).ready(function () {
        var line_no = cm.getCursor().line;
        var id = get_selected_id();
        var input = {
            'id': id,
            'line_id': cells[id]['proof'][line_no]['id']
        };

        input['theorem'] = prompt('Enter rewrite theorem');
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/rewrite-goal",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result);
            }
        })
    })
}

function set_line(cm) {
    $(document).ready(function () {
        var line = cm.getLine(cells[get_selected_id()].edit_line_number);
        var input = {
            'id': get_selected_id(),
            'line': line
        };
        var data = JSON.stringify(input);
        display_running();

        $.ajax({
            url: "/api/set-line",
            type: "POST",
            data: data,
            success: function (result) {
                display_checked_proof(result);
            }
        })
    })
}

function apply_backward_step_thm(cm) {
    var id = get_selected_id();
    var click_line_number = cells[id].click_line_number;
    var ctrl_click_line_numbers = cells[id].ctrl_click_line_numbers;
    if (click_line_number === -1) {
        return;
    } else {
        match_thm(cm);
    }
}

function match_thm(cm) {
    var id = get_selected_id();
    var click_line_number = cells[id].click_line_number;
    var ctrl_click_line_numbers = cells[id].ctrl_click_line_numbers;
    $(document).ready(function () {
        var conclusion_id = [];
        ctrl_click_line_numbers.forEach(val => {
            conclusion_id.push(cells[get_selected_id()]['proof'][val]['id']);
        });
        var data = {
            'id': get_selected_id(),
            'target_id': cells[get_selected_id()]['proof'][click_line_number]['id'],
            'conclusion_id': conclusion_id
        };

        $.ajax({
            url: "/api/match_thm",
            type: "POST",
            data: JSON.stringify(data),
            success: function (result) {
                display_match_thm(result);
            }
        })
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
    return display_str(editor, p[0], line_no, ch, {css: color});
}

// Display a list of pairs with highlight
function display_highlight_strs(editor, ps, line_no, ch) {
    $.each(ps, function (i, p) {
        ch = display_highlight_str(editor, p, line_no, ch);
    })
    return ch;
}

// Print a single line.
function display_line(id, line_no) {
    var editor = get_selected_editor();
    var line = cells[id]['proof'][line_no];
    var ch = 0;

    edit_flag = true;
    // Display id in bold
    ch = display_str(editor, line.id + ': ', line_no, ch, {css: 'font-weight: bold'});
    // Display theorem with highlight
    if (line.th.length > 0) {
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
    edit_flag = false;
}

// Display the given content in the textarea with the given id.
function display(id) {
    var editor = get_selected_editor();
    edit_flag = true;
    editor.setValue('');
    edit_flag = false;
    var cell = cells[id]['proof'];
    $.each(cell, function (line_no) {
        display_line(id, line_no);
        edit_flag = true;
        var len = editor.getLineHandle(line_no).text.length;
        editor.replaceRange('\n', {line: line_no, ch: len}, {line: line_no, ch: len + 1});
        edit_flag = false;
    });

    cells[get_selected_id()].readonly_lines.length = 0;
    for (var i = 0; i < editor.lineCount(); i++)
        cells[get_selected_id()].readonly_lines.push(i);
}

function display_match_thm(result) {
    if ('ths' in result) {
        $('.code-cell.selected .match-thm').append(
            $(`<pre>Theorems: (Ctrl-B)</pre><div class="thm-content"></div>`)
        );
        for (var i in result['ths']) {
            $('.code-cell.selected .thm-content').append(
                $(`<pre>${result['ths'][i]}</pre>`)
            );
        }
        $('.code-cell.selected .thm-content').append(
            $(`<a href="#" class="backward-step">Other backward step</a>`)
        )
    }
}

function get_match_thm() {
    var match_thm_list = [];
    $('.code-cell.selected .thm-content pre').each(function () {
            match_thm_list.push($(this).text())
        }
    );
    return match_thm_list;
}

