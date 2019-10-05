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

    // Mapping of colors.
    rp: function (x) {
        if (x === 0)
            return 'normal';
        if (x === 1)
            return 'bound';
        if (x === 2)
            return 'var';
        if (x === 3)
            return 'tvar';
    },

    // Convert a list of (s, color) to html form.
    highlight_html: function (lst) {
        var output = '';
        for (let i = 0; i < lst.length; i++) {
            output = output + '<span class="' + this.rp(lst[i][1]) + '">' + lst[i][0].replace(/ /g, '&nbsp;') + '</span>'
        }
        return output
    },

    get_status_color: function (item) {
        if (item.proof === undefined) {
            return 'red';
        } else if (item.num_gaps > 0) {
            return 'chocolate';
        } else {
            return 'green';
        }
    },

    adjust_input_size: function (input) {
        var text = $(input).val();
        var test_width = $(input).closest('form').find('pre.test-width');
        test_width.text(text);
        var min_width = $(input).attr('min-width');
        $(input).css('width', test_width.css('width'));
        if (min_width !== undefined && $(input).width() < Number(min_width)) {
            $(input).css('width', min_width + 'px');
        }
        $(input).attr('rows', text.split('\n').length);
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
