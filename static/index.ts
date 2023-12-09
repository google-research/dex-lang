// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd


function oops<T>() : T {throw new Error("oops")}

const body         : Element = document.getElementById("main-output") ?? oops()
const hoverInfoDiv : Element = document.getElementById("hover-info")  ?? oops()

type CellId = number
type SrcId  = number
type HTMLString = string
type Div = Element
type Status = "Waiting" | "Running" | "Complete"
type HighlightType = "HighlightGroup" |  "HighlightLeaf"
type Span = [Div, Div]
type SpanMap      = Map<SrcId, Span>
type HighlightMap = Map<SrcId, [HighlightType, SrcId]>
type HoverMap     = Map<SrcId, HTMLString>

type Cell = {
    cellId       : CellId;
    root         : Div;
    status       : Div;
    lineNums     : Div;
    source       : Div;
    results      : Div;
    spanMap      : SpanMap;
    highlightMap : HighlightMap;
    hoverMap     : HoverMap}
type HsSourceInfo =
    {tag: "SIGroupTree"; contents: HsMaybe<HsGroupTree>} |
    {tag: "SITypeInfo" ; contents: [SrcId, string][]}
type HsRenderedSourceBlock = {
    rsbLine       : number;
    rsbNumLines   : number;
    rsbBlockId    : CellId;
    rsbLexemeList : SrcId[];
    rsbHtml       : HTMLString }
type HsRenderedOutput =
    {tag: "RenderedTextOut"   ; contents: string                  } |
    {tag: "RenderedHtmlOut"   ; contents: HTMLString              } |
    {tag: "RenderedSourceInfo"; contents: HsSourceInfo            } |
    {tag: "RenderedPassResult"; contents: PassName                } |
    {tag: "RenderedMiscLog"   ; contents: string                  } |
    {tag: "RenderedError"     ; contents: [HsMaybe<SrcId>, string]}
type PassName = string
type PassInfo = string | null
type LexemeId = SrcId
type LexemeSpan = [LexemeId, LexemeId]
type HsGroupTree = {
    gtSrcId          : SrcId;
    gtSpan           : LexemeSpan;
    gtChildren       : [HsGroupTree];
    gtIsAtomicLexeme : boolean }

type HsMaybe<T> = {tag:"Just"; contents:T} | {tag: "Nothing"}
type HsOverwrite<T> = {tag:"OverwriteWith"; contents:T} | {tag: "NoChange"}
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

const cells = new Map<CellId, Cell>()
const curHighlights : Div[] = []  // HTML elements currently highlighted
let frozenHover:boolean = false;

function processUpdates(msg:HsMsg) {
    for (let i = 0; i < msg.orderedNodesUpdate.numDropped; i++) {
        let cell : Element = body.lastElementChild ?? oops()
        cell.remove();}
    msg.nodeMapUpdate.forEach(function (elt:[CellId, HsCellMapUpdate]) {
        const [cellId, update] = elt
        switch (update.tag) {
            case "Create":  // deliberate fallthrough
            case "Replace":
                const cell : Cell = createCell(cellId)
                initializeCell(cell, update.contents)
                break
            case "Update":
                updateCellContents(lookupCell(cellId), update.contents);}})
    msg.orderedNodesUpdate.newTail.forEach(function (cellId) {
        const cell : Cell = lookupCell(cellId);
        body.appendChild(cell.root);})
    msg.nodeMapUpdate.forEach(function (elt:[CellId, HsCellMapUpdate]) {
        const [cellId, update] = elt
        switch (update.tag) {
            case "Create":
                const cell : Cell = lookupCell(cellId)
                const lexemes : SrcId[] = update.contents[0].rsbLexemeList
                lexemes.map((lexemeId) => attachHovertip(cell, lexemeId))
                break
            case "Update": // nothing
        }})
}
function lookupCell(cellId: CellId) : Cell {
    return cells.get(cellId) ?? oops()
}
// Structure of each cell
// [cell]
//   [status] [line-nums] [contents]
//                          [source]
//                          [results]
//                            [result]
//                            [result]
function createCell(cellId: CellId) : Cell {
    const root : Div = document.createElement("div")
    root.className = "cell"
    const status   : Div = addChild(root, "status")
    const lineNums : Div = addChild(root, "line-nums")
    const contents : Div = addChild(root, "contents")
    const source   : Div = addChild(contents, "source")
    const results  : Div = addChild(contents, "results")
    source.innerHTML
    const cell : Cell = {
        cellId       : cellId,
        root         : root,
        status       : status,
        lineNums     : lineNums,
        source       : source,
        results      : results,
        spanMap      : new Map<SrcId, Span>(),
        highlightMap : new Map<SrcId, [HighlightType, SrcId]>(),
        hoverMap     : new Map<SrcId, HTMLString>()}
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
    if (frozenHover) return;
    hoverInfoDiv.innerHTML = ""
    curHighlights.map(function (element) {
        element.classList.remove("highlighted", "highlighted-leaf")})
    curHighlights.length = 0
}
function toggleFrozenHover() {
    if (frozenHover) {
        frozenHover = false
        removeHover()
    } else {
        frozenHover = true}
}
function attachHovertip(cell:Cell, srcId:SrcId) {
    let span = selectSpan(cell, srcId)
    span.addEventListener("mouseover", function (event:Event) {
        event.stopPropagation()
        applyHover(cell, srcId)})
    span.addEventListener("mouseout" , function (event:Event) {
        event.stopPropagation()
        removeHover()})
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
function selectSpan(cell:Cell, srcId:SrcId) : Div {
    const spanId : string = "#span_".concat(cell.cellId.toString(), "_", srcId.toString())
    return cell.source.querySelector(spanId) ?? oops()
}
function addClassToSrcNode(cell: Cell, srcId:SrcId, className:string) {
    // let span = getSpan(cellId, srcId)
    // if (span !== undefined) {
    //     let [l, r] = span
    //     let spans = spansBetween(selectSpan(cellId, l), selectSpan(cellId, r));
    //     spans.map(function (span) {
    //         span.classList.add(className)
    //         curHighlights.push(span)})}
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
        default:
            return oops()}
}
function setCellStatus(cell: Cell, status: Status) {
    cell.status.className = "status"
    cell.status.classList.add(cellStatusClass(status))
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
            case "RenderedSourceInfo":
                extendSourceInfo(cell, output.contents)
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
                    addClassToSrcNode(cell, maybeSrcId.contents, "err-span")}
                addErrResult(cell, errMsg)
                break
            default:
                // nothing
        }})
}
function extendSourceInfo(cell: Cell, info: HsSourceInfo) {
    switch (info.tag) {
        case "SITypeInfo":
            // TODO: this should really merge with previous rather than
            // clobbering it completely but for now we only expect to do this
            // once per cell so it's ok.
            cell.hoverMap = new Map(info.contents)
            break
        default:
            // nothing
    }
}
function applyHover(cell:Cell, srcId:SrcId) {
    if (frozenHover) return;
    applyHoverInfo(cell, srcId)
    applyHoverHighlights(cell, srcId)
}
function applyHoverInfo(cell:Cell, srcId:SrcId) {
    const hoverInfo : undefined | HTMLString = cell.hoverMap.get(srcId)
    if (hoverInfo !== undefined) {
        hoverInfoDiv.innerHTML = hoverInfo}
}
function applyHoverHighlights(cell:Cell, srcId:SrcId) {
    // TODO
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
                  body.addEventListener("click", function (event) {
                      event.stopPropagation()
                      toggleFrozenHover()})
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
