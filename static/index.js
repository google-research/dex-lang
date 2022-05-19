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

function renderLaTeX() {
    // Render LaTeX equations in prose blocks via KaTeX, if available.
    // Skip rendering if KaTeX is unavailable.
    if (typeof renderMathInElement == 'undefined') {
        return;
    }
    // Render LaTeX equations in prose blocks via KaTeX.
    var proseBlocks = document.querySelectorAll(".prose-block");
    Array.from(proseBlocks).map((proseBlock) =>
        renderMathInElement(proseBlock, katexOptions)
    );
}

/**
 * Rendering the Table of Contents / Navigation Bar
 * 2 key functions
 *  - `updateNavigation()` which inserts/updates the navigation bar
 *  - and it's helper `extractStructure()` which extracts the structure of the page
 *    and adds ids to heading elements.
*/
function updateNavigation() {
    function navItemList(struct) {
        var listEle = document.createElement('ol')
        struct.children.forEach(childStruct=>
            listEle.appendChild(navItem(childStruct))
        );
        return listEle;
    }
    function navItem(struct) {
        var a = document.createElement('a');
        a.appendChild(document.createTextNode(struct.text));
        a.title = struct.text;
        a.href = "#"+struct.id;

        var ele = document.createElement('li')
        ele.appendChild(a)
        ele.appendChild(navItemList(struct));
        return ele;
    }

    var navbarEle = document.getElementById("navbar")
    if (navbarEle === null) {  // create it
        navbarEle = document.createElement("div");
        navbarEle.id="navbar";
        navOuterEle = document.createElement("nav")
        navOuterEle.appendChild(navbarEle);
        document.body.prepend(navOuterEle);
    }

    navbarEle.innerHTML = ""
    var structure = extractStructure()
    navbarEle.appendChild(navItemList(structure));
}

function extractStructure() { // Also sets ids on h1,h2,...
    var headingsNodes = document.querySelectorAll("h1, h2, h3, h4, h5, h6");
    // For now we are just fulling going to regenerate the structure each time
    // Might be better if we made minimal changes, but 🤷

    // Extract the structure of the document
    var structure = {children:[]}
    var active = [structure.children];
    headingsNodes.forEach(
        function(currentValue, currentIndex) {
            currentValue.id = "s-" + currentIndex;
            var currentLevel = parseInt(currentValue.nodeName[1]);

            // Insert dummy levels up for any levels that are skipped
            for (var i=active.length; i < currentLevel; i++) {
                var dummy = {id: "", text: "", children: []}
                active.push(dummy.children);
                var parentList = active[i-1]
                parentList.push(dummy);
            }
            // delete this level and everything after
            active.splice(currentLevel, active.length);

            var currentStructure = {
                id: currentValue.id,
                text: currentValue.textContent,
                children: [],
            };
            active.push(currentStructure.children);

            var parentList = active[active.length-2]
            parentList.push(currentStructure);
        },
    );
    return structure;
}

/**
 * HTML rendering mode.
 * Static rendering is used for static HTML pages.
 * Dynamic rendering is used for dynamic HTML pages via `dex web`.
 *
 * @enum {string}
 */
var RENDER_MODE = Object.freeze({
  STATIC: "static",
  DYNAMIC: "dynamic",
})

/**
 * Renders the webpage.
 * @param {RENDER_MODE} renderMode The render mode, either static or dynamic.
 */
function render(renderMode) {
    if (renderMode == RENDER_MODE.STATIC) {
        // For static pages, simply call rendering functions once.
        renderLaTeX();
        updateNavigation();
    } else {
        // For dynamic pages (via `dex web`), listen to update events.
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
            renderLaTeX();
            updateNavigation();
        };
    }
}
