// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd


function oops<T>() : T {throw new Error("oops")}

const body         : Element = document.getElementById("main-output") ?? oops()
const hoverInfoDiv : Element = document.getElementById("hover-info")  ?? oops()
const minimap      : Element = document.getElementById("minimap") ?? oops()

type CellId = number
type SrcId  = number
type LexemeId  = number
type HTMLString = string
type Div = Element
type Status = "Waiting" | "Running" | "Complete" | "CompleteWithErrors" | "Inert"

type HighlightType = "HighlightGroup" |  "HighlightLeaf" | "HighlightError"
type Highlight    = [SrcId, HighlightType]

type HsMaybe<T> = {tag:"Just"; contents:T} | {tag: "Nothing"}
type HsOverwrite<T> = {tag:"OverwriteWith"; contents:T} | {tag: "NoChange"}

type FocusMap = Map<LexemeId, SrcId>
type TreeMap  = Map<SrcId, TreeNode>
type TreeNode = {
    srcId      : SrcId
    span       : [Div, Div] | null ;
    highlights : Highlight[];
    text       : HTMLString}
type Cell = {
    cellId       : CellId;
    root         : Div;
    lineNums     : Div;
    source       : Div;
    results      : Div;
    status       : Div;
    curStatus    : Status | null ;
    sourceText   : string;
    focusMap     : FocusMap;
    treeMap      : TreeMap}
type HsRenderedSourceBlock = {
    rsbLine       : number;
    rsbNumLines   : number;
    rsbBlockId    : CellId;
    rsbLexemeList : SrcId[];
    rsbText       : string;
    rsbHtml       : HTMLString }
type HsRenderedOutput =
    {tag: "RenderedTextOut"   ; contents: string                  } |
    {tag: "RenderedHtmlOut"   ; contents: HTMLString              } |
    {tag: "RenderedPassResult"; contents: string                  } |
    {tag: "RenderedMiscLog"   ; contents: string                  } |
    {tag: "RenderedError"     ; contents: [HsMaybe<SrcId>, string]} |
    {tag: "RenderedTreeNodeUpdate" ; contents: [SrcId, HsTreeNodeMapUpdate][]} |
    {tag: "RenderedFocusUpdate"    ; contents: [LexemeId, SrcId][]}

type HsFocusMap = Map<LexemeId, SrcId>
type HsTreeNodeState = {
    tnSpan        : [LexemeId, LexemeId]
    tnHighlights  : Highlight[]
    tnText        : HTMLString}
type HsTreeNodeUpdate = {
    tnuHighlights : HsOverwrite<Highlight[]>;
    tnuText       : HsOverwrite<HTMLString>}
type HsTreeNodeMapUpdate =
    {tag: "Create" ; contents: HsTreeNodeState}  |
    {tag: "Replace"; contents: HsTreeNodeState}  |
    {tag: "Update" ; contents: HsTreeNodeUpdate} |
    {tag: "Delete"}
type HsCellState = [HsRenderedSourceBlock, Status, HsRenderedOutput[]]
type HsCellUpdate = [HsOverwrite<Status>, HsRenderedOutput[]]
type HsCellMapUpdate =
    {tag: "Create" ; contents: HsCellState}  |
    {tag: "Replace"; contents: HsCellState}  |
    {tag: "Update" ; contents: HsCellUpdate} |
    {tag: "Delete"}
type HsMsg = {
    nodeMapUpdate : [CellId, HsCellMapUpdate][];
    orderedNodesUpdate : {
        numDropped : number;
        newTail    : CellId[]}}

const orderedCells : Cell[] = []
const cells = new Map<CellId, Cell>()
const curHighlights : Div[] = []  // HTML elements currently highlighted

function processUpdates(msg:HsMsg) {
    dropCells(msg.orderedNodesUpdate.numDropped)
    msg.nodeMapUpdate.forEach(function (elt:[CellId, HsCellMapUpdate]) {
        const [cellId, update] = elt
        switch (update.tag) {
            case "Create":  // deliberate fallthrough
            case "Replace":
                const cell : Cell = createCell(cellId)
                initializeCell(cell, update.contents)
                orderedCells.push(cell)
                break
            case "Update":
                updateCellContents(lookupCell(cellId), update.contents);}})
    msg.orderedNodesUpdate.newTail.forEach(function (cellId) {
        const cell : Cell = lookupCell(cellId);
        body.appendChild(cell.root)
        if (cell.curStatus !== "Inert") {
            minimap.appendChild(cell.status)}})
    msg.nodeMapUpdate.forEach(function (elt:[CellId, HsCellMapUpdate]) {
        const [cellId, update] = elt
        switch (update.tag) {
            case "Create":
                const cell : Cell = lookupCell(cellId)
                const lexemes : SrcId[] = update.contents[0].rsbLexemeList
                attachStatusHovertip(cell)
                lexemes.map((lexemeId) => attachHovertip(cell, lexemeId))
                break
            case "Update": // nothing
        }})
}
function dropCells(n:number) {
    for (let i = 0; i < n; i++) {
        const cell : Cell = orderedCells.pop() ?? oops()
        cell.root.remove()
        cell.status.remove()}
}
function lookupCell(cellId: CellId) : Cell {
    return cells.get(cellId) ?? oops()
}
// Structure of each cell
// [cell]
//   [line-nums] [contents]
//                 [source]
//                 [results]
//                   [result]
//                   [result]
function createCell(cellId: CellId) : Cell {
    const root : Div = document.createElement("div")
    const cellHtmlId : string =  "cell_".concat(cellId.toString())
    root.id = cellHtmlId
    root.className = "cell"
    const lineNums : Div = addChild(root, "line-nums")
    const contents : Div = addChild(root, "contents")
    const source   : Div = addChild(contents, "source")
    const results  : Div = addChild(contents, "results")
    const status : Div = document.createElement("a")
    status.setAttribute("href", "#".concat(cellHtmlId))
    status.className = "status"
    const cell : Cell = {
        cellId       : cellId,
        root         : root,
        lineNums     : lineNums,
        source       : source,
        results      : results,
        status       : status,
        curStatus    : null,
        sourceText   : "",
        focusMap     : new Map<LexemeId, SrcId>(),
        treeMap      : new Map<SrcId, TreeNode>()}
    cells.set(cellId, cell)
    return cell
}
function initializeCell(cell: Cell, state: HsCellState) {
    const [source, status, outs] = state
    cell.source.innerHTML = source.rsbHtml
    for (let i=0; i < source.rsbNumLines; i++) {
        const lineNum : number = i + source.rsbLine
        const s : string = lineNum.toString().concat("\n")
        appendText(cell.lineNums, s)}
    cell.sourceText = source.rsbText
    setCellStatus(cell, status)
    extendCellOutput(cell, outs)
}
function updateCellContents(cell:Cell, update:HsCellUpdate) {
    let [statusUpdate, outputs] = update;
    if (statusUpdate["tag"] == "OverwriteWith") {
        setCellStatus(cell, statusUpdate["contents"])}
    extendCellOutput(cell, outputs)
}
function removeHover() {
    hoverInfoDiv.innerHTML = ""
    curHighlights.map(function (element) {
        element.classList.remove("highlight-group", "highlight-leaf")})
    curHighlights.length = 0
}
function attachStatusHovertip(cell:Cell) {
    cell.status.addEventListener("mouseover", function (event:Event) {
        event.stopPropagation()
        setHoverInfo(cell.sourceText)})
    cell.status.addEventListener("mouseout", function (event:Event) {
        event.stopPropagation()
        removeHover()})
}
function attachHovertip(cell:Cell, srcId:SrcId) {
    let span = selectSpan(cell, srcId)
    if (span !== null) {
        span.addEventListener("mouseover", function (event:Event) {
            event.stopPropagation()
            applyCellHover(cell, srcId)})
        span.addEventListener("mouseout" , function (event:Event) {
            event.stopPropagation()
            removeHover()})}
}
function addChild(div:Div, className:string) : Div {
    const child = document.createElement("div")
    child.className = className
    div.appendChild(child)
    return child
}
function appendText(div:Div, s:string) {
    div.appendChild(document.createTextNode(s))
}
function selectSpan(cell:Cell, srcId:SrcId) : Div | null {
    const spanId : string = "#span_".concat(cell.cellId.toString(), "_", srcId.toString())
    return cell.source.querySelector(spanId)
}
function spansBetween(l:Div, r:Div) : Div[] {
    let spans : Div[] = []
    let curL : Div | null = l
    while (curL !== null && !(Object.is(curL, r))) {
        spans.push(curL);
        curL = curL.nextElementSibling;}
    spans.push(r)
    return spans
}
function cellStatusClass(status: Status) : string {
    switch (status) {
        case "Waiting":
            return "status-waiting"
        case "Running":
            return "status-running"
        case "Complete":
            return "status-success"
        case "CompleteWithErrors":
            return "status-err"
        case "Inert":
            return "status-inert"
        default:
            return oops()}
}
function setDivStatus(div: Div, status: Status) {
    div.classList.remove("status-waiting", "status-running", "status-success")
    div.classList.add(cellStatusClass(status))
}
function setCellStatus(cell: Cell, status: Status) {
    cell.curStatus = status
    setDivStatus(cell.lineNums, status)
    setDivStatus(cell.status  , status)
}
function addTextResult(cell:Cell, contents:string) {
    const child = addChild(cell.results, "text-result")
    appendText(child, contents)
}
function addErrResult(cell:Cell, contents:string) {
    const child = addChild(cell.results, "err-result")
    appendText(child, contents)
}
function addHTMLResult(cell:Cell, contents:HTMLString) {
    const child = addChild(cell.results, "html-result")
    child.innerHTML = contents
}
function extendCellOutput(cell: Cell, outputs:HsRenderedOutput[]) {
    outputs.forEach((output:HsRenderedOutput) => {
        switch (output.tag) {
            case "RenderedTextOut":
                addTextResult(cell, output.contents)
                break
            case "RenderedHtmlOut":
                addHTMLResult(cell, output.contents)
                break
            case "RenderedPassResult":
                // TODO: show passes
                break
            case "RenderedMiscLog":
                // TODO: show logs
                break
            case "RenderedError":
                const [maybeSrcId, errMsg] = output.contents
                if (maybeSrcId.tag == "Just") {
                    const node : TreeNode = cell.treeMap.get(maybeSrcId.contents) ?? oops()
                    highlightTreeNode(false, node, "HighlightError")}
                addErrResult(cell, errMsg)
                break
            case "RenderedTreeNodeUpdate":
                output.contents.forEach(function (elt:[SrcId, HsTreeNodeMapUpdate]) {
                    const [srcId, update] = elt
                    applyTreeNodeUpdate(cell, srcId, update)})
                break
            case "RenderedFocusUpdate":
                output.contents.forEach(function (elt:[LexemeId, SrcId]) {
                    const [lexemeId, srcId] = elt
                    cell.focusMap.set(lexemeId, srcId)})
                break
            default:
                // nothing
        }})
}
function applyTreeNodeUpdate(cell:Cell, srcId:SrcId, update:HsTreeNodeMapUpdate) {
    switch (update.tag) {
        case "Create":  // deliberate fallthrough
        case "Replace":
            const s : HsTreeNodeState = update.contents
            const [l, r] = s.tnSpan
            const range = computeRange(cell, l, r)
            const treeNode : TreeNode = {
                srcId      : srcId,
                span       : range,
                highlights : s.tnHighlights,
                text       : s.tnText}
            cell.treeMap.set(srcId, treeNode)
            break
        case "Update":
            const nodeUpdate : HsTreeNodeUpdate = update.contents
            const curTreeNode : TreeNode = cell.treeMap.get(srcId) ?? oops()
            const text = nodeUpdate.tnuText
            if (text.tag == "OverwriteWith") {
                curTreeNode.text = text.contents}
            const hl = nodeUpdate.tnuHighlights
            if (hl.tag == "OverwriteWith") {
                curTreeNode.highlights = hl.contents}
            break}
}
function computeRange(cell:Cell, l:SrcId, r:SrcId) : [Div, Div] | null {
    const lDiv = selectSpan(cell, l)
    const rDiv = selectSpan(cell, r)
    if (lDiv !== null && rDiv !== null) {
        return [lDiv, rDiv]
    } else {
        return null}
}
function applyCellHover(cell:Cell, srcId:LexemeId) {
    const focus : undefined | SrcId = cell.focusMap.get(srcId)
    if (focus !== undefined) {
        applyFocus(cell, focus)
    }
}
function applyFocus(cell:Cell, focus:SrcId) {
    const focusNode : TreeNode = cell.treeMap.get(focus) ?? oops()
    focusNode.highlights.forEach((h:Highlight) => {
        const [sid, ty] = h
        const node : TreeNode = cell.treeMap.get(sid) ?? oops()
        highlightTreeNode(true, node, ty)})
    setHoverInfo(focusNode.text)
}
function setHoverInfo(s:string) {
    hoverInfoDiv.innerHTML = ""
    appendText(hoverInfoDiv, s)
}
function computeHighlightClass(h:HighlightType) : string {
    switch (h) {
        case "HighlightGroup":
            return "highlight-group"
        case "HighlightLeaf":
            return "highlight-leaf"
        case "HighlightError":
            return "highlight-error"
    }
}
function highlightTreeNode(isTemporary: boolean, node: TreeNode, highlightType:HighlightType) {
    const highlightClass : string = computeHighlightClass(highlightType)
    if (node.span !== null) {
        let [l, r] = node.span
        let spans = spansBetween(l, r)
        spans.map(function (span) {
            span.classList.add(highlightClass)
            if (isTemporary) {curHighlights.push(span)}})}
}
type RenderMode = "Static" | "Dynamic"
function render(renderMode:RenderMode) {
    switch (renderMode) {
        case "Static":
            // For static pages, simply call rendering functions once.
            // renderLaTeX(document);
            break
        case "Dynamic":
          const source = new EventSource("/getnext");
          source.onmessage = function(event) {
              const msg = JSON.parse(event.data);
              if (msg == "start") {
                  body.innerHTML = ""
                  cells.clear()
                  return
              } else {
                  processUpdates(msg)
              }};}
}
const katexOptions = {
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

function renderLaTeX(root:Div) {
    // // Render LaTeX equations in prose blocks via KaTeX, if available.
    // // Skip rendering if KaTeX is unavailable.
    // let renderMathInElement: any
    // if (typeof renderMathInElement == 'undefined') {
    //     return;
    // }
    // // Render LaTeX equations in prose blocks via KaTeX.
    // const proseBlocks = root.querySelectorAll(".prose-block");
    // Array.from(proseBlocks).map((proseBlock) =>
    //     renderMathInElement(proseBlock, katexOptions)
    // );
}
