function high_light(list) {
    var type = '';
    $.each(list, function (i, val) {
        type = type + '<tt class="' + rp(val[1]) + '">' + val[0] + '</tt>';
    });
    return type
}
