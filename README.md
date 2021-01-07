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
  * [Mandelbrot set](https://google-research.github.io/dex-lang/examples/mandelbrot.html)
  * [Ray tracer](https://google-research.github.io/dex-lang/examples/raytrace.html)
  * [Estimating pi](https://google-research.github.io/dex-lang/examples/pi.html)
  * [Hamiltonian Monte Carlo](https://google-research.github.io/dex-lang/examples/mcmc.html)
  * [ODE integrator](https://google-research.github.io/dex-lang/oexamples/de-integrator.html)
  * [Sierpinski triangle](https://google-research.github.io/dex-lang/examples/sierpinski.html)
  * [Basis function regression](https://google-research.github.io/dex-lang/examples/regression.html)
  * [Brownian bridge](https://google-research.github.io/dex-lang/examples/brownian_motion.html)

🚨 **Dex is an experimental research project at an early stage of
development. Expect monstrous bugs and razor-sharp edges!**

🤝 **Contributions welcome!** See our issue tracker for [good first issues](https://github.com/google-research/dex-lang/labels/good%20first%20issue), or browse by [thematic labels](https://github.com/google-research/dex-lang/labels).

## Dependencies

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 9
    * Ubuntu/Debian: `apt-get install llvm-9-dev`
    * macOS: `brew install llvm@9`
      * Make sure `llvm@9` is on your `PATH` before building. Example: `export PATH="$(brew --prefix llvm@9)/bin:$PATH"`
  * Install clang (may be installed together with llvm)
    * Ubuntu/Debian: `apt-get install clang`
    * macOS: installs with llvm
  * Install libpng (often included by default in *nix platforms)
    * Ubuntu/Debian: `apt-get install libpng-dev`
    * macOS: `brew install libpng`

## Building

 * Build Dex in development mode: `make`
 * Run tests in development mode: `make tests`
 * Install a release version of Dex: `make install`

The default installation directory is `$HOME/.local/bin`, so make sure to add
that directory to `$PATH` after installing Dex. To install Dex somewhere else,
set the `PREFIX` environment variable before running `make install`. For
example, `PREFIX=$HOME make install` installs `dex` in `$HOME/bin`.

It is convenient to set up a `dex` alias (e.g. in `.bashrc`) for running Dex in
development mode:

```console
# Linux:
alias dex="stack exec dex --"

# macOS:
alias dex="stack exec --stack-yaml=stack-macos.yaml dex --"
```

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script examples/pi.dx`
  * Live-updated notebook display `dex web examples/pi.dx` (html) or `dex watch
    examples/pi.dx` (terminal).

## License

BSD-3

This is an early-stage research project, not an official Google product.
