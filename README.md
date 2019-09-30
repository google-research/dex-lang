Setup
=====

- Install [stack](https://www.haskellstack.org)
- Install LLVM: `apt-get install llvm-7-dev`
- Build the C extension: `make libcod`

Workflow
========

- Compile: `stack build`
- Run tests: `make all-tests`
- Start REPL: `stack exec dex`
