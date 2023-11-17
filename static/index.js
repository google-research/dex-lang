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

function lookup_address(cell, address) {
    var node = cell
    for (i = 0; i < address.length; i++) {
        node = node.children[address[i]]
    }
    return node
}

function renderHovertips(root) {
    var spans = root.querySelectorAll(".code-span");
    Array.from(spans).map((span) => attachHovertip(span));
}

function attachHovertip(node) {
    node.addEventListener("mouseover", (event) => highlightNode(     event, node));
    node.addEventListener("mouseout" , (event) => removeHighlighting(event, node));
}

function highlightNode(event, node) {
    event.stopPropagation();
    node.style.backgroundColor = "lightblue";
    node.style.outlineColor = "lightblue";
    node.style.outlineStyle = "solid";
    Array.from(node.children).map(function (child) {
        if (isCodeSpanOrLeaf(child)) {
            child.style.backgroundColor = "yellow";
        }
    })
}

function isCodeSpanOrLeaf(node) {
  return node.classList.contains("code-span") || node.classList.contains("code-span-leaf")

}

function removeHighlighting(event, node) {
    event.stopPropagation();
    node.style.backgroundColor = null;
    node.style.outlineColor = null;
    node.style.outlineStyle = null;
    Array.from(node.children).map(function (child) {
        if (isCodeSpanOrLeaf(child)) {
          child.style.backgroundColor = null;
        }
    })
}

function renderLaTeX(root) {
    // Render LaTeX equations in prose blocks via KaTeX, if available.
    // Skip rendering if KaTeX is unavailable.
    if (typeof renderMathInElement == 'undefined') {
        return;
    }
    // Render LaTeX equations in prose blocks via KaTeX.
    var proseBlocks = root.querySelectorAll(".prose-block");
    Array.from(proseBlocks).map((proseBlock) =>
        renderMathInElement(proseBlock, katexOptions)
    );
}

/**
 * Rendering the Table of Contents / Navigation Bar
 * 2 key functions
 *  - `updateNavigation()` which inserts/updates the navigation bar
 *  - and its helper `extractStructure()` which extracts the structure of the page
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

// mapping from server-provided NodeID to HTML id
var cells = {};
var body = document.getElementById("main-output");

/**
 * Renders the webpage.
 * @param {RENDER_MODE} renderMode The render mode, either static or dynamic.
 */
function render(renderMode) {
    if (renderMode == RENDER_MODE.STATIC) {
        // For static pages, simply call rendering functions once.
        renderLaTeX(document);
        renderHovertips(document);
        updateNavigation();
    } else {
        // For dynamic pages (via `dex web`), listen to update events.
        var source = new EventSource("/getnext");
        source.onmessage = function(event) {
            var msg = JSON.parse(event.data);
            if (msg == "start") {
                body.innerHTML = "";
                cells = {}
                return
            } else {
                process_update(msg);
            }
        };
    }
}

function set_cell_contents(cell, contents) {
    var line_num = contents[0][0];
    var source_text = contents[0][1];
    var line_num_div = document.createElement("div");

    line_num_div.innerHTML = line_num.toString();
    line_num_div.className = "line-num";
    cell.innerHTML = ""
    cell.appendChild(line_num_div);
    cell.innerHTML += source_text
    var results     = contents[1];
    tag             = results["tag"]
    if (tag == "Waiting") {
        cell.className = "cell waiting-cell";
    } else if (tag == "Running") {
        cell.className = "cell running-cell";
    } else if (tag == "Complete") {
        cell.className = "cell complete-cell";
        cell.innerHTML += results["contents"]
    } else {
        console.error(tag);
    }
    renderLaTeX(cell);
    renderHovertips(cell);
}

function process_update(msg) {
    var cell_updates = msg["nodeMapUpdate"]["mapUpdates"];
    var num_dropped  = msg["orderedNodesUpdate"]["numDropped"];
    var new_tail     = msg["orderedNodesUpdate"]["newTail"];

    // drop_dead_cells
    for (i = 0; i < num_dropped; i++) {
        body.lastElementChild.remove();}

    Object.keys(cell_updates).forEach(function (node_id) {
        var update = cell_updates[node_id];
        var tag = update["tag"]
        var contents = update["contents"]
        if (tag == "Create") {
            var cell = document.createElement("div");
            cells[node_id] = cell;
            set_cell_contents(cell, contents)
        } else if (tag == "Update") {
            var cell = cells[node_id];
            set_cell_contents(cell, contents);
        } else if (tag == "Delete") {
            delete cells[node_id]
        } else {
            console.error(tag);
        }
    });

    // append_new_cells
    new_tail.forEach(function (node_id) {
        body.appendChild(cells[node_id]);
    });

}
