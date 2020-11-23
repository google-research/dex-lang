# Dex [![Test status](https://github.com/google-research/dex-lang/workflows/Tests/badge.svg)](https://github.com/google-research/dex-lang/actions?query=workflow%3ATests)
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

## Dependencies

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 9
    * `apt-get install llvm-9-dev` on Ubuntu/Debian,
    * `brew install llvm@9` on macOS, and ensure it is on your `PATH` e.g. via `export PATH="$(brew --prefix llvm@9)/bin:$PATH"` before building.

## Building

 * Build Dex in development mode: `make`
 * Run tests in development mode: `make tests`
 * Install a release version of Dex: `make install`

The default installation directory is `$HOME/.local/bin` so make sure to add that
directory to `$PATH` once you install Dex. If you'd like to install it somewhere else
make sure to have the `PREFIX` environment variable set when you run `make install`.
For example `PREFIX=$HOME make install` would install `dex` in `$HOME/bin`.

While working in development mode, it is convenient to set up a `dex` alias
(e.g. in .bashrc): `alias dex="stack exec dex --"`,
or if on macOS: `alias dex="stack --stack-yaml=stack-macos.yaml exec -- dex"`.

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script examples/pi.dx`
  * Live-updated notebook display `dex web examples/pi.dx` (html) or `dex watch
    examples/pi.dx` (terminal).

## License

BSD-3

This is an early-stage research project, not an official Google product.
