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
                processUpdate(msg);
            }
        };
    }
}

function attachHovertip(cellCtx, srcId) {
    let span = selectSpan(cellCtx, srcId);
    span.addEventListener("mouseover", (event) => toggleSpan(event, cellCtx, srcId));
    span.addEventListener("mouseout" , (event) => toggleSpan(event, cellCtx, srcId));}

function selectSpan(cellCtx, srcId) {
    let [cell, blockId,  ,  ] = cellCtx
    return cell.querySelector("#span_".concat(blockId.toString(), "_", srcId.toString()));}

function getHighlightClass(highlightType) {
    if (highlightType == "HighlightGroup") {
        return "highlighted";
    } else if (highlightType == "HighlightLeaf") {
        return "highlighted-leaf";
    } else {
        throw new Error("Unrecognized highlight type");
    }
}

function toggleSpan(event, cellCtx, srcId) {
    event.stopPropagation();
    let [ , , focusMap, highlightMap] = cellCtx;
    let focus = focusMap[srcId.toString()];
    if (focus == null) return;
    let highlights = highlightMap[focus.toString()];
    highlights.map(function (highlight) {
        let [highlightType, [l, r]] = highlight;
        let spans = spansBetween(selectSpan(cellCtx, l), selectSpan(cellCtx, r));
        let highlightClass = getHighlightClass(highlightType);
        spans.map(function (span) {
            span.classList.toggle(highlightClass);
    })})}

function spansBetween(l, r) {
    let spans = []
    while (l !== null && !(Object.is(l, r))) {
        spans.push(l);
        l = l.nextSibling;
    }
    spans.push(r)
    return spans;}

function setCellContents(cell, contents) {
    let source  = contents[0];
    let results = contents[1];
    let lineNum    = source["jdLine"];
    let sourceText = source["jdHTML"];
    let lineNumDiv = document.createElement("div");
    lineNumDiv.innerHTML = lineNum.toString();
    lineNumDiv.className = "line-num";
    cell.innerHTML = ""
    cell.appendChild(lineNumDiv);
    cell.innerHTML += sourceText

    tag = results["tag"]
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
}

function processUpdate(msg) {
    let cell_updates = msg["nodeMapUpdate"]["mapUpdates"];
    let num_dropped  = msg["orderedNodesUpdate"]["numDropped"];
    let new_tail     = msg["orderedNodesUpdate"]["newTail"];

    // drop_dead_cells
    for (i = 0; i < num_dropped; i++) {
        body.lastElementChild.remove();}

    Object.keys(cell_updates).forEach(function (node_id) {
        let update = cell_updates[node_id];
        let tag = update["tag"]
        let contents = update["contents"]
        if (tag == "Create") {
            var cell = document.createElement("div");
            cells[node_id] = cell;
            setCellContents(cell, contents)
        } else if (tag == "Update") {
            var cell = cells[node_id];
            setCellContents(cell, contents);
        } else if (tag == "Delete") {
            delete cells[node_id]
        } else {
            console.error(tag);
        }
    });

    // append_new_cells
    new_tail.forEach(function (node_id) {
        let cell = cells[node_id];
        body.appendChild(cell);
    })

    Object.keys(cell_updates).forEach(function (node_id) {
        let update = cell_updates[node_id];
        let tag = update["tag"]
        let cell = cells[node_id];
        if (tag == "Create" || tag == "Update") {
            let source = update["contents"][0];
            let blockId      = source["jdBlockId"];
            let lexemeList   = source["jdLexemeList"];
            let focusMap     = source["jdFocusMap"];
            let highlightMap = source["jdHighlightMap"];
            cellCtx = [cell, blockId, focusMap, highlightMap];
            lexemeList.map(function (lexemeId) {attachHovertip(cellCtx, lexemeId)})
        }
    });
}
