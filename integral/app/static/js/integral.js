var cur_problem = [];

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
    const response = await axios.post("/open_file", JSON.stringify({'file_name': file_name}));
    content = response.data.content;
    console.log(content);
    var templ = _.template($('#template-contents').html());
    $('#content').html('');
    $.each(content, function (i, item) {
        $('#content').append(templ({id: i, item: item}));
    });
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, document.getElementById('content')]);
}

$(function () {
    $('#content').on('click', '.content-link', function () {
        initialize(this.name);
    });
})

function display_problem() {
    var templ = _.template($('#template-calc').html());
    $('#calc').html('');
    $.each(cur_problem, function (i, line) {
        $('#calc').append(templ({step_num: i+1, latex: line.latex, reason: line.reason}))
    });
    MathJax.Hub.Queue(["Typeset", MathJax.Hub, document.getElementById('calc')]);
}

async function initialize(problem) {
    const response = await axios.post("/initialize", JSON.stringify({'problem': problem}))
    cur_problem = [response.data]
    display_problem();
}

async function simplify() {
    if (cur_problem.length == 0)
        return;

    const problem = cur_problem[cur_problem.length-1].text;
    const response = await axios.post("/simplify", JSON.stringify({'problem': problem}))
    cur_problem.push(response.data);
    display_problem();
}

async function linearity() {
    if (cur_problem.length == 0)
        return;

    const problem = cur_problem[cur_problem.length-1].text;
    const response = await axios.post("/linearity", JSON.stringify({'problem': problem}))
    cur_problem.push(response.data);
    display_problem();
}

async function common_integral() {
    if (cur_problem.length == 0)
        return;

    const problem = cur_problem[cur_problem.length-1].text;
    const response = await axios.post("/common-integral", JSON.stringify({'problem': problem}))
    cur_problem.push(response.data);
    display_problem();
}
