// Name of the currently open file
var cur_file_name = undefined;

// Content of the current file
var content = undefined;

// Index of the current problem
var cur_id = undefined;

// Current calculation
var cur_calc = [];

// Import template files
var includes = $('[data-include]');
$.each(includes, function () {
    var file = "../" + $(this).data('include');
    $(this).load(file);
});

// When the user clicks on the button, 
// toggle between hiding and showing the dropdown content
function menu_file() {
    $(".dropdown-content").removeClass("show");
    document.getElementById("menu-file").classList.toggle("show");
}
function menu_calc() {
    $(".dropdown-content").removeClass("show");
    document.getElementById("menu-calc").classList.toggle("show");
}
function menu_action() {
    $(".dropdown-content").removeClass("show");
    document.getElementById("menu-action").classList.toggle("show");
}

// Close the dropdown menu if the user clicks outside of it
window.onclick = function (event) {
    if (!event.target.matches('.dropbtn')) {
        $(".dropdown-content").removeClass("show");
    }
}

async function open_file() {
    const file_name = prompt("Enter file name:", "test");
    const response = await axios.post("/open_file", JSON.stringify({ file_name: file_name }));
    content = response.data.content;
    var templ = _.template($('#template-contents').html());
    $('#content').html('');
    $.each(content, function (i, item) {
        $('#content').append(templ({ id: i, item: item }));
    });
    cur_file_name = file_name;
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, document.getElementById('content')]);
}

$(function () {
    $('#content').on('click', '.content-link', function () {
        cur_id = Number(this.getAttribute('item-id'));
        initialize(this.getAttribute('item-id'));
    });
})

function display_problem() {
    var templ = _.template($('#template-calc').html());
    $('#calc').html('');
    $.each(cur_calc, function (i, line) {
        if ('_latex_reason' in line)
            var reason = line._latex_reason;
        else
            var reason = line.reason;
        $('#calc').append(templ({ step_num: i + 1, latex: line.latex, reason: reason }))
    });
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, document.getElementById('calc')]);
}

async function initialize(item_id) {
    if ('calc' in content[item_id]) {
        cur_calc = Array.from(content[item_id].calc);  // create copy
    } else {
        const problem = content[item_id].problem;
        const response = await axios.post("/initialize", JSON.stringify({ problem: problem }))
        cur_calc = [response.data]
    }
    display_problem();
}

async function simplify() {
    if (cur_calc.length == 0)
        return;

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/simplify", JSON.stringify({ problem: problem }))
    cur_calc.push(response.data);
    display_problem();
}

async function linearity() {
    if (cur_calc.length == 0)
        return;

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/linearity", JSON.stringify({ problem: problem }))
    cur_calc.push(response.data);
    display_problem();
}

async function common_integral() {
    if (cur_calc.length == 0)
        return;

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/common-integral", JSON.stringify({ problem: problem }))
    cur_calc.push(response.data);
    display_problem();
}

function substitution() {
    if (cur_calc.length == 0)
        return;

    var templ = _.template($('#template-subst-dialog').html());
    $("#dialogs").html(templ({}));
    $("#subst-dialog").dialog();
}

async function do_substitution() {
    var var_name = document.getElementById('subst-var-name');
    var expr = document.getElementById('subst-expr');

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/substitution", JSON.stringify({
        problem: problem,
        var_name: var_name.value,
        expr: expr.value
    }));

    $("#subst-dialog").dialog("close");
    cur_calc.push(response.data);
    display_problem();
}

function integrate_by_parts() {
    if (cur_calc.length == 0)
        return;

    var templ = _.template($('#template-parts-dialog').html());
    $("#dialogs").html(templ({}));
    $("#parts-dialog").dialog({
        width: "400px"
    });
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, document.getElementById('#parts-dialog')]);

}

async function do_integrate_by_parts() {
    var parts_u = document.getElementById('parts-u');
    var parts_v = document.getElementById('parts-v');

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/integrate-by-parts", JSON.stringify({
        problem: problem,
        parts_u: parts_u.value,
        parts_v: parts_v.value
    }));

    $("#parts-dialog").dialog("close");
    cur_calc.push(response.data);
    display_problem();
}

async function polynomial_division(){
    if (cur_calc.length == 0)
        return;

    const problem = cur_calc[cur_calc.length - 1].text;
    const response = await axios.post("/polynomial-division", JSON.stringify({ problem: problem }))
    cur_calc.push(response.data);
    display_problem();
}

async function save_calc() {
    if (cur_file_name === undefined)
        return;

    if (cur_id === undefined)
        return;

    content[cur_id].calc = cur_calc;
    const response = await axios.post("/save-file", JSON.stringify({
        file_name: cur_file_name,
        content: content
    }));

    if (response.data.status === 'success') {
        alert("Saved " + content[cur_id].name);
    }
}

async function restart_calc() {
    const problem = content[cur_id].problem;
    const response = await axios.post("/initialize", JSON.stringify({ problem: problem }))
    cur_calc = [response.data]
    display_problem();
}

function restore_calc() {
    if ('calc' in content[cur_id]) {
        cur_calc = Array.from(content[cur_id].calc);  // create copy
        display_problem();
    }
}
