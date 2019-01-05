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
    var editor = get_selected_editor();
    var status_output = get_selected_output();

    if ("failed" in result) {
        status_output.innerHTML = result["failed"] + ": " + result["message"]
    } else {
        editor.setValue(result["proof"]);
        var num_gaps = result["report"]["num_gaps"];
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

function send_input() {
    $(document).ready(function () {
            var editor = get_selected_editor();
            var line_no = editor.getCursor().line;
            var input = {
                "id": get_selected_id(),
                "proof": editor.getValue()
            };
            var data = JSON.stringify(input);
            display_running();

            $.ajax({
                url: "/api/check-proof",
                type: "POST",
                data: data,
                success: function (result) {
                    display_checked_proof(result);
                    editor.setCursor(line_no, Number.MAX_SAFE_INTEGER);
                }
            })
        }
    )
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
    swal({
        title: 'Please enter the theorem used',
        html:
            '<input id="swal-input1" class="swal2-input">' +
            '<select id="swal-input2" class="swal2-select"></select>',
        onOpen: function () {
            init_select_abs()
        },
        showCancelButton: true,
        confirmButtonText: 'confirm',
        showLoaderOnConfirm: true,
        preConfirm: () => {
            var data = {
                'id': get_selected_id(),
                'line': line,
                'theorem': document.getElementById('swal-input1').value,
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

        input['theorem'] = prompt('Enter induction theorem and variable name')
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

        input['theorem'] = prompt('Enter rewrite theorem')
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
