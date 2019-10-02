
var cells = {};

function append_contents(key, contents) {
    if (key in cells) {
        var cell = cells[key];
    } else {
        var cell = document.createElement("div");
        cell.className = "cell";
        cells[key] = cell;
    }

    for (var i = 0; i < contents.length; i++) {
        var node = lookup_address(cell, contents[i][0])
        node.innerHTML += contents[i][1];
        console.log(node);
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
    var msg = JSON.parse(event.data);
    console.log(msg);
    var order    = msg[0];
    var contents = msg[1];
    for (var i = 0; i < contents.length; i++) {
        append_contents(contents[i][0], contents[i][1]);
    }
    // TODO: keys may appear twice, but they'll only show up once (html doesn't
    // allow repeated nodes). We need to make copies and keep them in sync.
    if (order != null) {
        var body = document.getElementById("main-output");
        body.innerHTML = "";
        for (var i = 0; i < order.val.length; i++) {
            body.appendChild(cells[order.val[i]]);
        }
    }
    render_plots();
};
