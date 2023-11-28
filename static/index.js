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

function selectSpan(cellCtx, srcId) {
    let [cell, blockId,  ,  ] = cellCtx
    return cell.querySelector("#span_".concat(blockId.toString(), "_", srcId.toString()));}

function attachHovertip(cellCtx, srcId) {
    let span = selectSpan(cellCtx, srcId);
    span.addEventListener("mouseover", (event) => toggleSpan(event, cellCtx, srcId));
    span.addEventListener("mouseout" , (event) => toggleSpan(event, cellCtx, srcId));}

function getParent(cellCtx, srcId) {
    let [ ,  , astInfo, ] = cellCtx;
    let parent = astInfo["astParent"][srcId.toString()]
    if (parent == undefined) {
        console.error(srcId, astInfo);
        throw new Error("Can't find parent");
    } else {
        return parent;
    }}

function getChildren(cellCtx, srcId) {
    let [ ,  , astInfo, ] = cellCtx;
    let children = astInfo["astChildren"][srcId.toString()]
    if (children == undefined) {
        return [];
    } else {
        return children;
    }}

function isLeafGroup(span) {
    return span !== null && (span.classList.contains("keyword") || span.classList.contains("symbol"))
}

function toggleSrcIdHighlighting(cellCtx, srcId) {
    let maybeLeaf = selectSpan(cellCtx, srcId)
    // XXX: this is a bit of a hack. We should probably collect information
    // about node types on the Haskell side
    if (isLeafGroup(maybeLeaf)) {
        maybeLeaf.classList.toggle("highlighted-leaf");
    } else {
        getSrcIdSpans(cellCtx, srcId).map(function (span) {
          span.classList.toggle("highlighted");
    })}}

// All HTML spans associated with the srcId (these should be contiguous)
function getSrcIdSpans(cellCtx, srcId) {
    let [ , , , nodeSpans] = cellCtx;
    let [leftSrcId, rightSrcId] = nodeSpans[srcId];
    return spansBetween(selectSpan(cellCtx, leftSrcId), selectSpan(cellCtx, rightSrcId));}

function spansBetween(l, r) {
    let spans = []
    while (l !== null && !(Object.is(l, r))) {
        spans.push(l);
        l = l.nextSibling;
    }
    spans.push(r)
    return spans;}

function toggleSpan(event, cellCtx, srcId) {
    event.stopPropagation();
    let parentId = getParent(cellCtx, srcId);
    let siblingIds = getChildren(cellCtx, parentId);
    siblingIds.map(function (siblingId) {
        toggleSrcIdHighlighting(cellCtx, siblingId)
    })}

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
        cell = cells[node_id];
        body.appendChild(cell);
    })

    // add hovertips
    new_tail.forEach(function (node_id) {
        cell = cells[node_id];
        var update = cell_updates[node_id];
        if (update["tag"] == "Create") {
            var source = update["contents"][0];
            var blockId    = source["jdBlockId"];
            var astInfo    = source["jdASTInfo"];
            var lexemeList = source["jdLexemeList"];
            var astLims    = source["jdASTLims"];
            cellCtx = [cell, blockId, astInfo, astLims];
            lexemeList.map(function (lexemeId) {attachHovertip(cellCtx, lexemeId)})
        }
    });
}

