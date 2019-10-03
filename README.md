Setup
=====

- Install [stack](https://www.haskellstack.org)
- Install LLVM 7, e.g. `apt-get install llvm-7-dev`

Building
========

- Build Dex `make` (or `make-no-web` on non-Linux)
- Run tests: `make tests`
- Set up alias (e.g. in .bashrc) `alias dex=stack exec dex --`

Running
=======

- Traditional REPL: `dex repl`
- Execute script: `dex script example/tutorial.dx`
- Notebook interface: `dex web example/tutorial.dx`
