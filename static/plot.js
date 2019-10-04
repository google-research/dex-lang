// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

function render_plots() {
  nodes = document.getElementsByClassName("plot-pending");
  for (var i = 0; i < nodes.length; i++) {
      var plot_div = nodes[i];
      plot_div.className="plot-finished";
      var data = JSON.parse(plot_div.childNodes[0].innerHTML);
      Plotly.plot(plot_div, [data]);
  }
}
