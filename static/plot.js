
function render_plots() {
  nodes = document.getElementsByClassName("plot-pending");
  for (var i = 0; i < nodes.length; i++) {
      var plot_div = nodes[i];
      plot_div.className="plot-finished";
      var data = JSON.parse(plot_div.childNodes[0].innerHTML);
      Plotly.plot(plot_div, [data]);
  }
}
