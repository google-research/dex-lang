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
    let highlights = lookupSrcMap(highlightMap, cellId, srcId)
    if (highlights == null) return
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
function getStatusClass(status) {
    if (status == "Waiting") {
        return "waiting-cell";
    } else if (status == "Running") {
        return "running-cell";
    } else if (status == "Complete") {
        return "complete-cell";
    } else {
        throw new Error("Unrecognized status type");
    }
}
function spansBetween(l, r) {
    let spans = []
    while (l !== null && !(Object.is(l, r))) {
        spans.push(l);
        l = l.nextSibling;}
    spans.push(r)
    return spans
}
function setCellStatus(cell, status) {
    cell.className = "class"
    cell.classList.add(getStatusClass(status))
}

function setCellContents(cellId, cell, contents) {
    let [source, status, result]  = contents;
    let lineNum    = source["rsbLine"];
    let sourceText = source["rsbHtml"];
    let lineNumDiv = document.createElement("div");
    lineNumDiv.innerHTML = lineNum.toString();
    lineNumDiv.className = "line-num";
    cell.innerHTML = ""
    cell.appendChild(lineNumDiv)
    setCellStatus(cell, status)
    cell.innerHTML += sourceText
    renderLaTeX(cell)
    extendCellResult(cellId, cell, result)
}
function extendCellResult(cellId, cell, result) {
    let resultText = result["rrHtml"]
    if (resultText !== "") {
        cell.innerHTML += resultText
    }
    highlightMap[cellId] = result["rrHighlightMap"]
    hoverInfoMap[cellId] = result["rrHoverInfoMap"]
}
function updateCellContents(cellId, cell, contents) {
    let [statusUpdate, result] = contents;
    if (statusUpdate["tag"] == "OverwriteWith") {
        setCellStatus(cell, statusUpdate["contents"])}
    extendCellResult(cellId, cell, result)
}
function processUpdate(msg) {
    let cellUpdates = msg["nodeMapUpdate"]["mapUpdates"];
    let numDropped  = msg["orderedNodesUpdate"]["numDropped"];
    let newTail     = msg["orderedNodesUpdate"]["newTail"];

    // drop_dead_cells
    for (i = 0; i < numDropped; i++) {
        body.lastElementChild.remove();}

    Object.keys(cellUpdates).forEach(function (cellId) {
        let update = cellUpdates[cellId];
        let tag = update["tag"]
        let contents = update["contents"]
        if (tag == "Create" || tag == "Replace") {
            let cell = document.createElement("div");
            cells[cellId] = cell;
            setCellContents(cellId, cell, contents)
        } else if (tag == "Update") {
            let cell = cells[cellId];
            updateCellContents(cellId, cell, contents);
        } else if (tag == "Delete") {
            delete cells[cellId]
        } else {
            console.error(tag);
        }});

    // append_new_cells
    newTail.forEach(function (cellId) {
        let cell = selectCell(cellId);
        body.appendChild(cell);})

    Object.keys(cellUpdates).forEach(function (cellId) {
        let update = cellUpdates[cellId]
        let tag = update["tag"]
        if (tag == "Create" || tag == "Replace") {
            let update = cellUpdates[cellId];
            let source = update["contents"][0];
            let lexemeList = source["rsbLexemeList"];
            lexemeList.map(function (lexemeId) {attachHovertip(cellId, lexemeId.toString())})}});
}
