
nodes = document.getElementsByClassName("heatmap");
for (var i = 0; i < nodes.length; i++) {
    var plot_div = nodes[i];
    var data = JSON.parse(plot_div.childNodes[0].innerHTML);
    Plotly.plot(plot_div, [data]);
}
