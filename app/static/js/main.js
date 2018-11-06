(function ($) {
    var pageNum = 0;
    $(document).ready(function () {
        let output = CodeMirror.fromTextArea(document.getElementById("output-iframe"), {
            lineNumbers: true,
            readOnly: "nocursor",
            scrollbarStyle: "overlay",
        });
        output.setSize("auto", window.innerHeight);
        output.setValue("");
        $('#add-page').click();
        document.getElementById('open-file').addEventListener('change', function (e) {
            e = e || window.event;

            var files = this.files;
            var editor = document.querySelector('.tab-pane.active textarea + .CodeMirror').CodeMirror;
            editor.setValue("");
            for (var i = 0, f; f = files[i]; i++) {
                var reader = new FileReader();
                reader.onload = (function (file) {
                    return function (e) {
                        editor.setValue(editor.getValue() + this.result);
                    };
                })(f);
                reader.readAsText(f);
            }
        });
        document.getElementById("run-button").addEventListener('click', send_input);
    });

    function init_editor(editor_id = "code1") {
        let editor = CodeMirror.fromTextArea(document.getElementById(editor_id), {
            mode: "text/groovy",
            mode: "text/x-java",
            mode: "text/x-python",
            lineNumbers: true,
            theme: "material",
            lineWrapping: false,
            foldGutter: true,
            gutters: ["CodeMirror-linenumbers", "CodeMirror-foldgutter"],
            matchBrackets: true,
            scrollbarStyle: "overlay",
            extraKeys: {
                "Shift-Ctrl-Enter": function () {

                }
            }
        });
        editor.setSize("auto", window.innerHeight);
        editor.setValue("");
        editor.on("keyHandled", function (cm, name) {
            if (name === "Shift-Ctrl-Enter") {
                send_input()
            }
        });
    }

    function send_input() {
        $(document).ready(function () {
                var input = {};
                var counter = 1;
                var reg_blank = /^\s*$/g;
                var editor = document.querySelector('.tab-pane.active textarea + .CodeMirror').CodeMirror;
                editor.eachLine(line => {
                    if (!reg_blank.test(line.text))
                        input[counter++] = line.text;
                });
                var data = JSON.stringify(input);

                $.ajax({
                    url: "/api/check-proof",
                    type: "POST",
                    data: data,
                    success: function (result) {
                        let output = document.querySelector("#output-iframe + .CodeMirror").CodeMirror;
                        for (var i in result) {
                            if (output.getValue() === "")
                                output.setValue(output.getValue() + result[i]);
                            else
                                output.setValue(output.getValue() + "\n" + result[i]);
                        }
                    }
                })
            }
        )
    }

    function clear_output() {
        let output = document.querySelector("#output-iframe + .CodeMirror").CodeMirror;
        output.setValue("");
    }

    function switch_check_box() {
        if ($('#check-box').hasClass("is-checked")) {
            $('#check-box').removeClass("is-checked");
            $('#auto-run').removeClass("is-checked");
            $('#auto-run').removeAttr("aria-checked", "true");
        }
        else {
            $('#check-box').addClass("is-checked");
            $('#auto-run').addClass("is-checked");
            $('#auto-run').attr("aria-checked", "true");
        }
    }

    function remove_page() {
        pageNum = 1;
        $('#codeTab > li').each(function () {
            var pageId = $(this).children('a').attr('href');
            if (pageId === "#code1-pan") {
                return true;
            }
            pageNum++;
            $(this).children('a').html('Page ' + pageNum +
                '<button id="close_tab" type="button" ' +
                'title="Remove this page">×</button>');
        });
    }

    $('#add-page').click(function () {
        pageNum++;
        $('#codeTab').append(
            $('<li class="nav-item"><a  class="nav-link" ' +
                'data-toggle="tab"' +
                'href="#code' + pageNum + '-pan">' +
                'Page ' + pageNum +
                '<button id="close_tab" type="button" ' +
                'title="Remove this page">×</button>' +
                '</a></li>'));
        let class_name = 'tab-pane fade active newCodeMirror';
        if (pageNum === 1)
            class_name = 'tab-pane fade in active';
        $('#codeTabContent').append(
            $('<div class="' + class_name + '" id="code' + pageNum + '-pan">' +
                '<label for="code' + pageNum + '"></label> ' +
                '<textarea' + ' id="code' + pageNum + '""></textarea>'));
        init_editor("code" + pageNum);
        $('#codeTab a[href="#code' + pageNum + '-pan"]').tab('show');
        $('.newCodeMirror').each(function () {
            $(this).removeClass('active')
        });
    });

    $('#codeTab').on('click', ' li a #close_tab', function () {
        var tabId = $(this).parents('li').children('a').attr('href');
        $(this).parents('li').remove('li');
        $(tabId).remove();
        remove_page();
        $('#codeTab a:first').tab('show');
    });

    $('#codeTab').on("click", "a", function (e) {
        e.preventDefault();
        $(this).tab('show');
    });

    $('#clear').on("click", function () {
        clear_output();
    })

    $('#check-box').on("click", function () {
        switch_check_box();
    })

    $('#check-box-inner').on("click", function () {
        switch_check_box();
    })
})
(jQuery);