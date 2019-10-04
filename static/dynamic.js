// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
    var msg = JSON.parse(event.data);
    var order    = msg[0];
    var contents = msg[1];
    for (var i = 0; i < contents.length; i++) {
        append_contents(contents[i][0], contents[i][1]);
    }
    if (order != null) {
        var new_cells = {};
        var body = document.getElementById("main-output");
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
    render_plots();
};
