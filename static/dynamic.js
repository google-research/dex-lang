// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

var katexOptions = {
    delimiters: [
        {left: "$$", right: "$$", display: true},
        {left: "\\[", right: "\\]", display: true},
        {left: "$", right: "$", display: false},
        {left: "\\(", right: "\\)", display: false}
    ],
    // Enable commands that load resources or change HTML attributes
    // (e.g. hyperlinks): https://katex.org/docs/security.html.
    trust: true
};

var cells = {};

function append_contents(key, contents) {
    if (key in cells) {
        var cur_cells = cells[key];
    } else {
        var cell = document.createElement("div");
        cell.className = "cell";
        cells[key] = [cell];
        var cur_cells = [cell];
    }
    for (var i = 0; i < contents.length; i++) {
        for (var j = 0; j < cur_cells.length; j++) {
            var node = lookup_address(cur_cells[j], contents[i][0])
            node.innerHTML += contents[i][1];
        }
    }
}

function lookup_address(cell, address) {
    var node = cell
    for (i = 0; i < address.length; i++) {
        node = node.children[address[i]]
    }
    return node
}

var source = new EventSource("/getnext");
source.onmessage = function(event) {
    var body = document.getElementById("main-output");
    var msg = JSON.parse(event.data);
    if (msg == "start") {
        body.innerHTML = "";
        cells = {}
        return
    }
    var order    = msg[0];
    var contents = msg[1];
    for (var i = 0; i < contents.length; i++) {
        append_contents(contents[i][0], contents[i][1]);
    }
    if (order != null) {
        var new_cells = {};
        body.innerHTML = "";
        for (var i = 0; i < order.val.length; i++) {
            var key = order.val[i]
            var cur_cells = cells[key]
            if (cur_cells.length == 0) {
                var cur_cell = new_cells[key][0].cloneNode(true)
            } else {
                var cur_cell = cur_cells.pop()
                if (key in new_cells) {
                    new_cells[key].push(cur_cell);
                } else {
                    new_cells[key] = [cur_cell];
                }
            }
            body.appendChild(cur_cell);
        }
        Object.assign(cells, new_cells);
    }
    // Render LaTeX equations via KaTeX.
    renderMathInElement(body, katexOptions);
};
