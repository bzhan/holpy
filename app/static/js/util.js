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

// Display a list of (s, color) in html form.
function high_light(list) {
    var type = '';
    $.each(list, function (i, val) {
        type = type + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
    });
    return type
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
