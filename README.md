# Dex

Dex (short for "index") is a research language for array processing in the
Haskell/ML family. The goal of the project is to explore questions about:

  * Type systems for array programming
  * Mathematical program transformations like differentiation and integration
  * User-directed compilation to parallel hardware
  * Interactive and incremental numerical programming and visualization

To learn more, check out our
[workshop paper](https://openreview.net/pdf?id=rJxd7vsWPS)
or look at these example programs:

  * [Tutorial](examples/tutorial.dx)
  * [Mandelbrot set](examples/mandelbrot.dx)
  * [Estimating pi](examples/pi.dx)
  * [Sierpinsky triangle](examples/sierpinsky.dx)

## Setup

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 7, e.g. `apt-get install llvm-7-dev`

## Building

 * Build Dex `make` (or `make-no-web` on non-Linux)
 * Run tests: `make tests`
 * Set up alias (e.g. in .bashrc) `alias dex=stack exec dex --`

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script example/tutorial.dx`
  * Notebook interface: `dex web example/tutorial.dx`

## License

Apache 2.0

This is an early-stage research project, not an official Google product.
