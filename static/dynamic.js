
function new_output_cell(output) {
    console.log(output);
    var body = document.getElementById("main-output");
    var source = output["source"];
    var instr = output["instr"];
    if ("unevaluated" in instr) {
        var cell = add_node(body, "output-cell", "");
        add_node(cell, "source", source);
        add_node(cell, "result-unevaluated", "");
    } else if ("result" in instr) {
        var cell = add_node(body, "output-cell", "");
        add_node(cell, "source", source);
        result = instr["result"];
        if ("text" in result) {
            add_node(cell, "result-text", result["text"]);
        } else if ("plot" in result) {
            plot_div = add_node(cell, "plot-output", "");
            Plotly.plot(plot_div, [result["plot"]]);
        }
    } else if ("error" in instr) {
        var cell = add_node(body, "err-cell", "");
        add_node(cell, "source", source);
        add_node(cell, "result-text", instr["error"]);
    } else if ("source_only" in instr) {
        var cell = add_node(body, "decl-cell", "");
        add_node(cell, "source", source);
    }
    return cell;
};

function add_node(parent, classname, html) {
    var newnode = document.createElement("div");
    newnode.className = classname;
    newnode.innerHTML = html;
    parent.appendChild(newnode);
    return newnode;
}

var source = new EventSource("/getnext");
source.onmessage = function(event) {
    var results = JSON.parse(event.data)["FreshPage"];
    var body = document.getElementById("main-output");
    while (body.firstChild) {
       body.removeChild(body.firstChild);
    }
    for (var i = 0; i < results.length; i++) {
        new_output_cell(results[i]);
    }
    // document.getElementById("main-output").innerHTML = event.data;
};
