# Dex [![Test status](https://travis-ci.org/google-research/dex-lang.svg?branch=master)](https://travis-ci.org/google-research/dex-lang)
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
  * [MNIST nearest-neighbor classifier](https://google-research.github.io/dex-lang/mnist-nearest-neighbors.html)

Please note that Dex is an experimental research project at an early stage of
development. We welcome contributions. There's plenty of work to do!

## Setup

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 9, e.g. `apt-get install llvm-9-dev` on Ubuntu/Debian.
    On macOS, the best approach seems to be to build LLVM from source,
    [as described here](https://github.com/google-research/dex-lang/issues/2#issuecomment-557793009).

## Building

 * Build Dex: `make`
 * Run tests: `make tests`
 * Set up alias (e.g. in .bashrc) `alias dex="stack exec dex --"`

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script examples/tutorial.dx`
  * Notebook interface: `dex web examples/tutorial.dx`

## License

BSD-3

This is an early-stage research project, not an official Google product.
