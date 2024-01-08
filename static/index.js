"use strict";
// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd
var _a, _b, _c;
function oops() { throw new Error("oops"); }
var body = (_a = document.getElementById("main-output")) !== null && _a !== void 0 ? _a : oops();
var hoverInfoDiv = (_b = document.getElementById("hover-info")) !== null && _b !== void 0 ? _b : oops();
var minimap = (_c = document.getElementById("minimap")) !== null && _c !== void 0 ? _c : oops();
var orderedCells = [];
var cells = new Map();
function processUpdates(msg) {
    dropCells(msg.orderedNodesUpdate.numDropped);
    msg.nodeMapUpdate.forEach(function (elt) {
        var cellId = elt[0], update = elt[1];
        switch (update.tag) {
            case "Create": // deliberate fallthrough
            case "Replace":
                var cell = createCell(cellId);
                initializeCell(cell, update.contents);
                orderedCells.push(cell);
                break;
            case "Update":
                updateCellContents(lookupCell(cellId), update.contents);
        }
    });
    msg.orderedNodesUpdate.newTail.forEach(function (cellId) {
        var cell = lookupCell(cellId);
        body.appendChild(cell.root);
        if (cell.curStatus !== "Inert") {
            minimap.appendChild(cell.status);
        }
    });
    msg.nodeMapUpdate.forEach(function (elt) {
        var cellId = elt[0], update = elt[1];
        switch (update.tag) {
            case "Create":
                var cell_1 = lookupCell(cellId);
                var lexemes = update.contents[0].rsbLexemeList;
                attachStatusHovertip(cell_1);
                lexemes.map(function (lexemeId) { return attachHovertip(cell_1, lexemeId); });
                break;
            case "Update": // nothing
        }
    });
}
function dropCells(n) {
    var _a;
    for (var i = 0; i < n; i++) {
        var cell = (_a = orderedCells.pop()) !== null && _a !== void 0 ? _a : oops();
        cell.root.remove();
        cell.status.remove();
    }
}
function lookupCell(cellId) {
    var _a;
    return (_a = cells.get(cellId)) !== null && _a !== void 0 ? _a : oops();
}
// Structure of each cell
// [cell]
//   [line-nums] [contents]
//                 [source]
//                 [results]
//                   [result]
//                   [result]
function createCell(cellId) {
    var root = document.createElement("div");
    var cellHtmlId = "cell_".concat(cellId.toString());
    root.id = cellHtmlId;
    root.className = "cell";
    var lineNums = addChild(root, "line-nums");
    var contents = addChild(root, "contents");
    var source = addChild(contents, "source");
    var results = addChild(contents, "results");
    var status = document.createElement("a");
    status.setAttribute("href", "#".concat(cellHtmlId));
    status.className = "status";
    var cell = {
        cellId: cellId,
        root: root,
        lineNums: lineNums,
        source: source,
        results: results,
        status: status,
        curStatus: null,
        sourceText: "",
        focusMap: new Map(),
        treeMap: new Map()
    };
    cells.set(cellId, cell);
    return cell;
}
function initializeCell(cell, state) {
    var source = state[0], status = state[1], outs = state[2];
    cell.source.innerHTML = source.rsbHtml;
    for (var i = 0; i < source.rsbNumLines; i++) {
        var lineNum = i + source.rsbLine;
        var s = lineNum.toString().concat("\n");
        appendText(cell.lineNums, s);
    }
    cell.sourceText = source.rsbText;
    setCellStatus(cell, status);
    extendCellOutput(cell, outs);
}
function updateCellContents(cell, update) {
    var statusUpdate = update[0], outputs = update[1];
    if (statusUpdate["tag"] == "OverwriteWith") {
        setCellStatus(cell, statusUpdate["contents"]);
    }
    extendCellOutput(cell, outputs);
}
function attachStatusHovertip(cell) {
    addHoverAction(cell.status, function () { return applyHoverStatus(cell); });
    if (cell.curStatus !== "Inert") {
        addHoverAction(cell.lineNums, function () { return applyHoverStatus(cell); });
    }
}
function applyHoverStatus(cell) {
    addHoverClass(cell.status, "status-hover");
    addHoverClass(cell.lineNums, "status-hover");
}
function attachHovertip(cell, srcId) {
    var span = selectSpan(cell, srcId);
    if (span !== null) {
        addHoverAction(span, function () { return applyCellHover(cell, srcId); });
    }
}
function selectSpan(cell, srcId) {
    var spanId = "#span_".concat(cell.cellId.toString(), "_", srcId.toString());
    return cell.source.querySelector(spanId);
}
function cellStatusClass(status) {
    switch (status) {
        case "Waiting":
            return "status-waiting";
        case "Running":
            return "status-running";
        case "Complete":
            return "status-success";
        case "CompleteWithErrors":
            return "status-err";
        case "Inert":
            return "status-inert";
        default:
            return oops();
    }
}
function setDivStatus(div, status) {
    div.classList.remove("status-waiting", "status-running", "status-success");
    div.classList.add(cellStatusClass(status));
}
function setCellStatus(cell, status) {
    cell.curStatus = status;
    setDivStatus(cell.lineNums, status);
    setDivStatus(cell.status, status);
}
function addTextResult(cell, contents) {
    var child = addChild(cell.results, "text-result");
    appendText(child, contents);
}
function addErrResult(cell, contents) {
    var child = addChild(cell.results, "err-result");
    appendText(child, contents);
}
function addHTMLResult(cell, contents) {
    var child = addChild(cell.results, "html-result");
    child.innerHTML = contents;
}
function extendCellOutput(cell, outputs) {
    outputs.forEach(function (output) {
        var _a;
        switch (output.tag) {
            case "RenderedTextOut":
                addTextResult(cell, output.contents);
                break;
            case "RenderedHtmlOut":
                addHTMLResult(cell, output.contents);
                break;
            case "RenderedPassResult":
                // TODO: show passes
                break;
            case "RenderedMiscLog":
                // TODO: show logs
                break;
            case "RenderedError":
                var _b = output.contents, maybeSrcId = _b[0], errMsg = _b[1];
                if (maybeSrcId !== null) {
                    var node = (_a = cell.treeMap.get(maybeSrcId)) !== null && _a !== void 0 ? _a : oops();
                    highlightTreeNode(false, node, "HighlightError");
                }
                addErrResult(cell, errMsg);
                break;
            case "RenderedTreeNodeUpdate":
                output.contents.forEach(function (elt) {
                    var srcId = elt[0], update = elt[1];
                    applyTreeNodeUpdate(cell, srcId, update);
                });
                break;
            case "RenderedFocusUpdate":
                output.contents.forEach(function (elt) {
                    var lexemeId = elt[0], srcId = elt[1];
                    cell.focusMap.set(lexemeId, srcId);
                });
                break;
            default:
            // nothing
        }
    });
}
function applyTreeNodeUpdate(cell, srcId, update) {
    var _a;
    switch (update.tag) {
        case "Create": // deliberate fallthrough
        case "Replace":
            var s = update.contents;
            var _b = s.tnSpan, l = _b[0], r = _b[1];
            var range = computeRange(cell, l, r);
            var treeNode = {
                srcId: srcId,
                span: range,
                highlights: s.tnHighlights,
                text: s.tnText
            };
            cell.treeMap.set(srcId, treeNode);
            break;
        case "Update":
            var nodeUpdate = update.contents;
            var node_1 = (_a = cell.treeMap.get(srcId)) !== null && _a !== void 0 ? _a : oops();
            nodeUpdate.tnuText.forEach(function (t) { node_1.text = node_1.text.concat(t, "\n"); });
            node_1.highlights = node_1.highlights.concat(nodeUpdate.tnuHighlights);
    }
}
function computeRange(cell, l, r) {
    var lDiv = selectSpan(cell, l);
    var rDiv = selectSpan(cell, r);
    if (lDiv !== null && rDiv !== null) {
        return [lDiv, rDiv];
    }
    else {
        return null;
    }
}
function applyCellHover(cell, srcId) {
    var focus = cell.focusMap.get(srcId);
    if (focus !== undefined) {
        applyFocus(cell, focus);
    }
}
function applyFocus(cell, focus) {
    var _a;
    var focusNode = (_a = cell.treeMap.get(focus)) !== null && _a !== void 0 ? _a : oops();
    focusNode.highlights.forEach(function (h) {
        var _a;
        var sid = h[0], ty = h[1];
        var node = (_a = cell.treeMap.get(sid)) !== null && _a !== void 0 ? _a : oops();
        highlightTreeNode(true, node, ty);
    });
    setHoverInfo(focusNode.text);
}
function setHoverInfo(s) {
    hoverInfoDiv.innerHTML = "";
    appendText(hoverInfoDiv, s);
}
function computeHighlightClass(h) {
    switch (h) {
        case "HighlightGroup":
            return "highlight-group";
        case "HighlightLeaf":
            return "highlight-leaf";
        case "HighlightError":
            return "highlight-error";
        case "HighlightScope":
            return "highlight-scope";
        case "HighlightBinder":
            return "highlight-binder";
        case "HighlightOcc":
            return "highlight-occ";
    }
}
function highlightTreeNode(isTemporary, node, highlightType) {
    var highlightClass = computeHighlightClass(highlightType);
    if (node.span !== null) {
        var _a = node.span, l = _a[0], r = _a[1];
        var spans = spansBetween(l, r);
        spans.map(function (span) {
            if (isTemporary) {
                addHoverClass(span, highlightClass);
            }
            else {
                span.classList.add(highlightClass);
            }
        });
    }
}
function render(renderMode, jsonData) {
    switch (renderMode) {
        case "Static":
            var req_1 = new XMLHttpRequest();
            req_1.open('GET', jsonData, true);
            req_1.responseType = 'json';
            req_1.onload = function () {
                processUpdates(req_1.response);
            };
            req_1.send();
            break;
        case "Dynamic":
            var source = new EventSource("/getnext");
            source.onmessage = function (event) {
                var msg = JSON.parse(event.data);
                if (msg == "start") {
                    resetState();
                }
                else {
                    processUpdates(msg);
                }
            };
    }
}
function resetState() {
    body.innerHTML = "";
    hoverInfoDiv.innerHTML = "";
    minimap.innerHTML = "";
    orderedCells.length = 0;
    curHighlights.length = 0;
    cells.clear();
}
// === hover system ===
var curHighlights = []; // HTML elements currently highlighted
function addHoverClass(div, className) {
    div.classList.add(className);
    curHighlights.push([div, className]);
}
function addHoverAction(div, handler) {
    div.addEventListener("mouseover", function (event) {
        event.stopPropagation();
        handler();
    });
    div.addEventListener("mouseout", function (event) {
        event.stopPropagation();
        removeHover();
    });
}
function removeHover() {
    hoverInfoDiv.innerHTML = "";
    curHighlights.map(function (elementAndClass) {
        var element = elementAndClass[0], className = elementAndClass[1];
        element.classList.remove(className);
    });
    curHighlights.length = 0;
}
// === utils ===
function spansBetween(l, r) {
    var spans = [];
    var curL = l;
    while (curL !== null && !(Object.is(curL, r))) {
        spans.push(curL);
        curL = curL.nextElementSibling;
    }
    spans.push(r);
    return spans;
}
function addChild(div, className) {
    var child = document.createElement("div");
    child.className = className;
    div.appendChild(child);
    return child;
}
function appendText(div, s) {
    div.appendChild(document.createTextNode(s));
}
