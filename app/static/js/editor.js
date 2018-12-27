var replace_obj = {
    "\\lambda": "λ",
    "%": "λ",
    "\\forall": "∀",
    "\\exists": "∃",
    "\\and": "∧",
    "&": "∧",
    "\\or": "∨",
    "|": "∨",
    "-->": "⟶",
    "~": "¬",
    "\\not": "¬",
    "=>": "⇒"
};

function unicode_replace(cm) {
    $(document).ready(function () {
        var cur_position = cm.getCursor()
        var line_number = cur_position.line
        var position = cur_position.ch
        var stri = cm.getRange({line: line_number, ch: 0}, cm.getCursor());
        for (var key in replace_obj) {
            l = key.length;
            if (stri.slice(-l) === key) {
                start_position = {line: line_number, ch: position - l};
                cm.replaceRange(replace_obj[key], start_position, cur_position);
            }
        }
    })
}
