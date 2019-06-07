// Mapping of colors.
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

// Convert a list of (s, color) to html form.
function highlight_html(lst) {
    var output = '';
    $.each(lst, function (i, val) {
        output = output + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
    });
    return output
}

// Return the status color of a theorem.
function get_status_color(ext) {
    if (ext.proof === undefined) {
        return 'red';
    } else if (ext.num_gaps > 0) {
        return 'yellow';
    } else {
        return 'green';
    }
}

function display_facts_and_goal(cm) {
    var id = get_selected_id();
    cm.getAllMarks().forEach(e => {
        if (e.css === 'background: red' || e.css == 'background: yellow') {
            e.clear()
        }
    });
    if (cells[id].goal !== -1) {
        goal_no = cells[id].goal;
        goal_line = cm.getLineHandle(goal_no).text;
        cm.markText({line: goal_no, ch: goal_line.length - 5},
                    {line: goal_no, ch: goal_line.length},
                    {css: 'background: red'});    
    }
    for (let fact_no of cells[id].facts) {
        fact_line = cm.getLineHandle(fact_no).text;
        cm.markText({line: fact_no, ch: 0}, {line: fact_no, ch: fact_line.length},
                    {css: 'background: yellow'});
    }
}

function print_search_res(res) {
    if (res._method_name === "apply_backward_step") {
        if (res._goal.length === 0)
            return res.theorem + " (b): (solves)"
        else
            return res.theorem + " (b): " + res._goal.join(", ");
    } else if (res._method_name === "apply_forward_step") {
        return res.theorem + " (f): have " + res._fact;
    } else if (res._method_name === "rewrite_goal") {
        if (res._goal.length === 0)
            return res.theorem + " (r): (solves)";
        else
            return res.theorem + " (r): " + res._goal.join(", ");
    } else if (res._method_name === "rewrite_fact") {
        return res.theorem + " (r): have " + res._fact;
    } else if (res._method_name === "introduction") {
        return "introduction";
    } else if (res._method_name === "rewrite_goal_with_prev") {
        if (res._goal.length === 0)
            return "rewrite with fact: (solves)"
        else
            return "rewrite with fact: " + res._goal.join(", ");
    } else if (res._method_name === "rewrite_fact_with_prev") {
        return "rewrite fact with fact";
    } else if (res._method_name === "apply_prev") {
        return "apply fact: " + res._goal.join(", ");
    } else if (res._method_name === "forall_elim") {
        return "forall elimination";
    } else if (res._method_name === "induction") {
        if ('var' in res)
            return "induction " + res.theorem + " var: " + res.var
        else
            return "induction " + res.theorem;
    } else if (res._method_name === "inst_exists_goal") {
        return "instantiate exists goal";
    } else if (res._method_name === "prove_avalI") {
        return "prove_avalI: (solves)";
    } else {
        return JSON.stringify(res);
    }
}