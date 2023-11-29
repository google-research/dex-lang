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

var body         = document.getElementById("main-output");
var hoverInfoDiv = document.getElementById("hover-info");

// State of the system beyond the HTML
var cells = {}
var frozenHover = false;
var curHighlights = [];  // HTML elements currently highlighted
var focusMap     = {}
var highlightMap = {}
var hoverInfoMap = {}

function removeHover() {
    if (frozenHover) return;
    hoverInfoDiv.innerHTML = ""
    curHighlights.map(function (element) {
        element.classList.remove("highlighted", "highlighted-leaf")})
    curHighlights = [];
}
function lookupSrcMap(m, cellId, srcId) {
    let blockMap = m[cellId]
    if (blockMap == null) {
        return null
    } else {
        return blockMap[srcId]}
}
function applyHover(cellId, srcId) {
    if (frozenHover) return;
    applyHoverInfo(cellId, srcId)
    applyHoverHighlights(cellId, srcId)
}
function applyHoverInfo(cellId, srcId) {
    let hoverInfo = lookupSrcMap(hoverInfoMap, cellId, srcId)
    hoverInfoDiv.innerHTML = srcId.toString() // hoverInfo
}
function applyHoverHighlights(cellId, srcId) {
    let focus = lookupSrcMap(focusMap, cellId, srcId)
    if (focus == null) return
    let highlights = lookupSrcMap(highlightMap, cellId, focus)
    highlights.map(function (highlight) {
        let [highlightType, [l, r]] = highlight
        let spans = spansBetween(selectSpan(cellId, l), selectSpan(cellId, r));
        let highlightClass = getHighlightClass(highlightType)
        spans.map(function (span) {
            span.classList.add(highlightClass)
            curHighlights.push(span)})})
}
function toggleFrozenHover() {
    if (frozenHover) {
        frozenHover = false
        removeHover()
    } else {
        frozenHover = true}
}
function attachHovertip(cellId, srcId) {
    let span = selectSpan(cellId, srcId)
    span.addEventListener("mouseover", function (event) {
        event.stopPropagation()
        applyHover(cellId, srcId)})
    span.addEventListener("mouseout" , function (event) {
        event.stopPropagation()
        removeHover()})}

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
                body.innerHTML = ""
                body.addEventListener("click", function (event) {
                    event.stopPropagation()
                    toggleFrozenHover()})
                cells = {}
                return
            } else {
                processUpdate(msg)}};}
}


function selectSpan(cellId, srcId) {
    return cells[cellId].querySelector("#span_".concat(cellId, "_", srcId))
}
function selectCell(cellId) {
    return cells[cellId]
}
function getHighlightClass(highlightType) {
    if (highlightType == "HighlightGroup") {
        return "highlighted";
    } else if (highlightType == "HighlightLeaf") {
        return "highlighted-leaf";
    } else {
        throw new Error("Unrecognized highlight type");
    }
}
function spansBetween(l, r) {
    let spans = []
    while (l !== null && !(Object.is(l, r))) {
        spans.push(l);
        l = l.nextSibling;
    }
    spans.push(r)
    return spans
}
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

    Object.keys(cell_updates).forEach(function (cellId) {
        let update = cell_updates[cellId];
        let tag = update["tag"]
        let contents = update["contents"]
        if (tag == "Create") {
            var cell = document.createElement("div");
            cells[cellId] = cell;
            setCellContents(cell, contents)
        } else if (tag == "Update") {
            var cell = cells[cellId];
            setCellContents(cell, contents);
        } else if (tag == "Delete") {
            delete cells[cellId]
        } else {
            console.error(tag);
        }});

    // append_new_cells
    new_tail.forEach(function (cellId) {
        let cell = selectCell(cellId);
        body.appendChild(cell);})

    Object.keys(cell_updates).forEach(function (cellId) {
        let update = cell_updates[cellId]
        let tag = update["tag"]
        if (tag == "Create" || tag == "Update") {
            let update = cell_updates[cellId];
            let source = update["contents"][0];
            focusMap[cellId]     = source["jdFocusMap"]
            highlightMap[cellId] = source["jdHighlightMap"]
            hoverInfoMap[cellId] = source["jsHoverInfoMap"]
            let lexemeList = source["jdLexemeList"];
            lexemeList.map(function (lexemeId) {attachHovertip(cellId, lexemeId.toString())})}});
}
