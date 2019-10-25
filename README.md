# Dex

Dex (named for "index") is a research language for array processing in the
Haskell/ML family. The goal of the project is to explore:

  * Type systems for array programming
  * Mathematical program transformations like differentiation and integration
  * User-directed compilation to parallel hardware
  * Interactive and incremental numerical programming and visualization

To learn more, check out our
[workshop paper](https://openreview.net/pdf?id=rJxd7vsWPS)
or these example programs:

  * [Tutorial](https://google-research.github.io/dex-lang/tutorial.html)
  * [Dex prelude](https://google-research.github.io/dex-lang/prelude.html)
  * [Mandelbrot set](https://google-research.github.io/dex-lang/mandelbrot.html)
  * [Estimating pi](https://google-research.github.io/dex-lang/pi.html)
  * [Sierpinsky triangle](https://google-research.github.io/dex-lang/sierpinsky.html)
  * [Basis function regression](https://google-research.github.io/dex-lang/regression.html)
  * [Brownian bridge](https://google-research.github.io/dex-lang/brownian_motion.html)

## Setup

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 7, e.g. `apt-get install llvm-7-dev`

## Building

 * Build Dex: `make`
 * Run tests: `make tests`
 * Set up alias (e.g. in .bashrc) `alias dex=stack exec dex --`

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script example/tutorial.dx`
  * Notebook interface: `dex web example/tutorial.dx`

## License

BSD-3

This is an early-stage research project, not an official Google product.
