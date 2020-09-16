# Dex [![Test status](https://github.com/google-research/dex-lang/workflows/Continuous%20integration/badge.svg)](https://travis-ci.org/google-research/dex-lang)
Dex (named for "index") is a research language for typed, functional array
processing. The goal of the project is to explore:

  * Type systems for array programming
  * Mathematical program transformations like differentiation and integration
  * User-directed compilation to parallel hardware
  * Interactive and incremental numerical programming and visualization

To learn more, check out our
[workshop paper](https://openreview.net/pdf?id=rJxd7vsWPS)
or these example programs:

  * [Dex prelude](https://google-research.github.io/dex-lang/prelude.html)
  * [Mandelbrot set](https://google-research.github.io/dex-lang/mandelbrot.html)
  * [Ray tracer](https://google-research.github.io/dex-lang/raytrace.html)
  * [Estimating pi](https://google-research.github.io/dex-lang/pi.html)
  * [Hamiltonian Monte Carlo](https://google-research.github.io/dex-lang/mcmc.html)
  * [ODE integrator](https://google-research.github.io/dex-lang/ode-integrator.html)
  * [Sierpinsky triangle](https://google-research.github.io/dex-lang/sierpinsky.html)
  * [Basis function regression](https://google-research.github.io/dex-lang/regression.html)
  * [Brownian bridge](https://google-research.github.io/dex-lang/brownian_motion.html)

Please note that Dex is an experimental research project at an early stage of
development. Contributions welcome!

## Setup

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 9, e.g. `apt-get install llvm-9-dev` on Ubuntu/Debian.
    For macOS, there's [some guidance here](https://github.com/google-research/dex-lang/issues/2#issuecomment-649896955).

## Building

 * Build Dex: `make`
 * Run tests: `make tests`
 * Set up a `dex` alias (e.g. in .bashrc) `alias dex="stack exec dex --"`

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script examples/pi.dx`
  * Live-updated notebook display `dex web examples/pi.dx` (html) or `dex watch
    examples/pi.dx` (terminal).

## License

BSD-3

This is an early-stage research project, not an official Google product.
