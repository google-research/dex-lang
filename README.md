# Dex [![Test status](https://github.com/google-research/dex-lang/workflows/Tests/badge.svg)](https://github.com/google-research/dex-lang/actions?query=workflow%3ATests)
Dex (named for "index") is a research language for typed, functional array
processing. The goal of the project is to explore:

  * Type systems for array programming
  * Mathematical program transformations like differentiation and integration
  * User-directed compilation to parallel hardware
  * Interactive and incremental numerical programming and visualization

To learn more, check out our
[paper](https://arxiv.org/abs/2104.05372),
our [tutorial](https://google-research.github.io/dex-lang/examples/tutorial.html)
or these example programs:

  * [Dex prelude](https://google-research.github.io/dex-lang/prelude.html)
  * [Mandelbrot set](https://google-research.github.io/dex-lang/examples/mandelbrot.html)
  * [Ray tracer](https://google-research.github.io/dex-lang/examples/raytrace.html)
  * [Estimating pi](https://google-research.github.io/dex-lang/examples/pi.html)
  * [Hamiltonian Monte Carlo](https://google-research.github.io/dex-lang/examples/mcmc.html)
  * [ODE integrator](https://google-research.github.io/dex-lang/examples/ode-integrator.html)
  * [Sierpinski triangle](https://google-research.github.io/dex-lang/examples/sierpinski.html)
  * [Basis function regression](https://google-research.github.io/dex-lang/examples/regression.html)
  * [Brownian bridge](https://google-research.github.io/dex-lang/examples/brownian_motion.html)
  * [Dynamic programming (Levenshtein distance)](https://google-research.github.io/dex-lang/examples/levenshtein-distance.html)
  * [Molecular dynamics simulation](https://google-research.github.io/dex-lang/examples/md.html)

Or for a more comprehensive look, there's

  * [The InDex](https://google-research.github.io/dex-lang/index.html) of all documents, libraries, and examples included in this repository.

🚨 **Dex is an experimental research project at an early stage of
development. Expect monstrous bugs and razor-sharp edges!**

🤝 **Contributions welcome!** See our issue tracker for [good first issues](https://github.com/google-research/dex-lang/labels/good%20first%20issue), or browse by [thematic labels](https://github.com/google-research/dex-lang/labels).

## Dependencies

  * Install [stack](https://www.haskellstack.org)
  * Install LLVM 12
    * Ubuntu/Debian: `apt-get install llvm-12-dev`
    * macOS: `brew install llvm@12`
      * Make sure `llvm@12` is on your `PATH` before building. Example: `export PATH="$(brew --prefix llvm@12)/bin:$PATH"`
  * Install clang 12 (may be installed together with llvm)
    * Ubuntu/Debian: `apt-get install clang-12`
    * macOS: installs with llvm
  * Install libpng (often included by default in *nix platforms)
    * Ubuntu/Debian: `apt-get install libpng-dev`
    * macOS: `brew install libpng`

## Installing

To build and install a release version of Dex run `make install`.

The default installation directory is `$HOME/.local/bin`, so make sure to add
that directory to `$PATH` after installing Dex. To install Dex somewhere else,
set the `PREFIX` environment variable before running `make install`. For
example, `PREFIX=$HOME make install` installs `dex` in `$HOME/bin`.

## Building

 * Build Dex in development (unoptimized) mode: `make`
 * Run tests in development mode: `make tests`

It is convenient to set up a `dex` alias (e.g. in `.bashrc`) for running Dex in
development mode:

```console
# Linux:
alias dex="stack exec dex -- --lib-path lib"

# macOS:
alias dex="stack exec --stack-yaml=stack-macos.yaml dex -- --lib-path lib"
```

You might also want to consider other development build targets:
  * `build-opt` for local optimized builds,
  * `build-dbg` for local debug builds,
  * `build-prof` for local optimized builds with profiling enabled.

Those non-standard targets require different aliases. Please consult the documentation
at the top of the [`makefile`](https://github.com/google-research/dex-lang/blob/main/makefile)
for detailed instructions.

### Haskell Language Server

In order to use [HLS](https://github.com/haskell/haskell-language-server) with
the Haskell code in this project:

- Install [ghcup](https://www.haskell.org/ghcup/)
- Run `ghcup install hls`
- Create a file in the root `dex` directory called `hie.yaml` with the following
contents:

```yaml
cradle:
  stack:
    stackYaml: "./stack-macos.yaml"  # Or stack.yaml if not on MacOS
```

Unfortunately one cannot dynamically select the `stack.yaml` file to use based
on the environment, and so one has to create an appropriate `hie.yaml` file
manually. This will be ignored by git.

This should work out of the box with Emacs' `lsp-haskell` package.

### Building with Nix

[Nix](https://nixos.org/) is a functional package manager and build system.

To build with vanilla Nix:
```bash
$ nix-build
```

To build with flakes-enabled Nix:
```bash
$ nix build .#dex
```
The resulting `dex` binary should be in `result/bin/dex`.

For development purposes, you can use a Nix environment with
```bash
$ nix-shell
$ nix develop  # With flakes
```
and use `make` to use Stack to build Dex.

## Running

  * Traditional REPL: `dex repl`
  * Execute script: `dex script examples/pi.dx`
  * Live-updated notebook display `dex web examples/pi.dx` (html) or `dex watch
    examples/pi.dx` (terminal).

## License

BSD-3

This is an early-stage research project, not an official Google product.
