var Util = {
    // Mapping for unicode-replace
    replace_obj: {
        "\\lambda": "λ",
        "%": "λ",
        "\\forall": "∀",
        "\\exists": "∃",
        "\\and": "∧",
        "&": "∧",
        "\\or": "∨",
        "|": "∨",
        "-->": "⟶",
        "<-->": "⟷",
        "~": "¬",
        "\\not": "¬",
        "=>": "⇒",
        "\\empty": "∅",
        "\\Inter": "⋂",
        "\\inter": "∩",
        "\\Union": "⋃",
        "\\union": "∪",
        "\\circ": "∘",
        "\\in": "∈",
        "\\subset": "⊆",
        "<=": "≤",
    },

    keywords: {
        'def': 'definition',
        'def.ax': 'constant',
        'thm': 'theorem',
        'thm.ax': 'axiom',
        'def.ind': 'fun',
        'def.pred': 'inductive',
        'type.ind': 'datatype'
    },

    replace_unicode: function (input, e) {
        var content = $(input).val().trim();
        var pos = input.selectionStart;
        if (pos !== 0 && e.keyCode === 9) {  // Enter
            var len = '';
            for (var key in this.replace_obj) {
                var l = key.length;
                if (content.substring(pos - l, pos) === key) {
                    if (e && e.preventDefault) {
                        e.preventDefault();
                    } else {
                        window.event.returnValue = false;
                    }
                    len = l;
                    content = content.slice(0, pos - len) + this.replace_obj[key] + content.slice(pos,);
                }
            }
            if (len) {
                $(input).val(content);
                input.setSelectionRange(pos - len + 1, pos - len + 1);
            }
        }       
    }
}

export default Util
