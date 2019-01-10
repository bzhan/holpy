var edit_flag = false;
var readonly_lines = [0];
var click_line_number = -1;
var ctrl_click_line_number = -1;
var edit_line_number = -1;
var cells = {};
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

function display_running() {
    var status_output = get_selected_output();
    status_output.innerHTML = "Running";
}

function display_checked_proof(result) {
    var status_output = get_selected_output();

    if ("failed" in result) {
        status_output.innerHTML = result["failed"] + ": " + result["message"];
        status_output.style.color = 'red';
    } else {
        edit_flag = true;
        edit_line_number = -1;
        add_cell_data(get_selected_id(), result['proof']);
        display(get_selected_id(), result['proof']);
        var num_gaps = result["report"]["num_gaps"];
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
}

function add_line_after(cm) {
    $(document).ready(function () {
            var line_number = cm.getCursor().line;
            var line = cm.getLine(line_number);
            var input = {
                "id": get_selected_id(),
                "line": line,
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
        }
    )
}

function remove_line(cm) {
    $(document).ready(function () {
        var line_number = cm.getCursor().line;
        var line = cm.getLine(line_number);
        var input = {
            "id": get_selected_id(),
            "line": line,
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
        var line_number = cm.getCursor().line;
        var line = cm.getLine(line_number);
        var input = {
            "id": get_selected_id(),
            "line": line,
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

function init_select_abs() {
    $(document).ready(function () {
        var event = {
            "event": "init_theorem_abs",
        };
        var data = JSON.stringify(event);

        $.ajax({
            url: "/api/init",
            type: "POST",
            data: data,
            success: function (result) {
            }
        })
    })
}

function apply_backward_step(cm) {
    var line_number = cm.getCursor().line;
    var line = cm.getLine(line_number);
    var title = '';
    if (click_line_number !== -1 && ctrl_click_line_number !== -1) {
        title = 'Target: ' + (click_line_number + 1) + '\nConclusion: ' + (ctrl_click_line_number + 1);
        line = cm.getLine(click_line_number);
    } else if (click_line_number !== -1 && ctrl_click_line_number === -1) {
        title = 'Target: ' + (click_line_number + 1);
    } else {
        title = 'Please enter the theorem userd';
    }
    swal({
        title: title,
        html:
            '<input id="swal-input1" class="swal2-input">',
        // '<select id="swal-input2" class="swal2-select"></select>',
        onOpen: function () {
            init_select_abs()
        },
        showCancelButton: true,
        confirmButtonText: 'confirm',
        showLoaderOnConfirm: true,
        focusConfirm: false,
        preConfirm: () => {
            document.querySelector('#swal-input1').focus();
            var id = '';
            var theorem = '';
            if (click_line_number !== -1 && ctrl_click_line_number !== -1) {
                id = cells[get_selected_id()][ctrl_click_line_number]['id'];
                theorem = document.getElementById('swal-input1').value + ', ' + id;
            } else if (click_line_number !== -1 && ctrl_click_line_number === -1) {
                theorem = document.getElementById('swal-input1').value;
            }
            var data = {
                'id': get_selected_id(),
                'line': line,
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
            click_line_number = -1;
            ctrl_click_line_number = -1;
            display_checked_proof(result['value']);
        }
    })
}

function apply_induction(cm) {
    $(document).ready(function () {
        var line_no = cm.getCursor().line;
        var line = cm.getLine(line_no);
        var input = {
            'id': get_selected_id(),
            'line': line
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
        var line = cm.getLine(line_no);
        var input = {
            'id': get_selected_id(),
            'line': line
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
        var line = cm.getLine(edit_line_number);
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

function split_proof_rule(line) {
    if (line.indexOf(': ') !== -1) {
        var list = line.split(': ');
        var id = list[0];
        var rest = list[1];
        id = id.trim();
        if (rest.indexOf(' by ') !== -1) {
            list = rest.split(' by ');
            var th = list[0];
            rest = list[1];
        } else {
            var th = '';
        }

        if (rest.indexOf(' ') !== -1) {
            list = rest.split(' ');
            var rule_name = list[0];
            list.splice(0, 1);
            rest = list.join(' ');
        } else {
            var rule_name = rest;
            rest = '';
        }
        rule_name = rule_name.trim();

        if (rest.indexOf('from') !== -1) {
            list = rest.split('from');
            var args = list[0];
            rest = list[1];
            list = rest.split(',');
            var prev = [];
            for (var i = 0; i < list.length; i++) {
                prev.push(list[i].trim())
            }
            return [id, rule_name, args.trim(), prev, th];
        } else {
            return [id, rule_name, rest.trim(), [], th];
        }
    }
}

function display(id, content) {
    var editor = get_selected_editor();
    var cell = cells[id];
    if (mod === 0) {
        editor.setValue(content);
    } else if (mod === 1) {
        var content_list = [];
        cell.forEach(e => {
            if (e.id.startsWith('var'))
                content_list.push(e.id + ': ' + e.rule_name);
            else
                content_list.push(e.id + ': ' + e.th)
        });
        var _content = content_list.join('\n');
        editor.setValue(_content);
    }
    readonly_lines.length = 0;
    for (var i = 0; i < editor.lineCount(); i++)
        readonly_lines.push(i);
}

function add_cell_data(id, content) {
    var cell = [];
    var result_list = content.split('\n');
    result_list.forEach(e => {
        var list = split_proof_rule(e);
        cell.push({
            'id': list[0],
            'rule_name': list[1],
            'args': list[2],
            'prev': list[3],
            'th': list[4]
        });
    });

    cells[id] = cell;
}
