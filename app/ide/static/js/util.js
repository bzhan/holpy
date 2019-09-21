var Util = {
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
            output = output + '<span class="' + this.rp(lst[i][1]) + '">' + lst[i][0].replace(/ /g, '&ensp;') + '</span>'
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
    }
}

export default Util
