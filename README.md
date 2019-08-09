Setup
=====

- Install LLVM
  sudo apt-get install llvm-7-dev
- Install C++ development environment if necessary (to build the LLVM bindings)
  (These are already present on a typical workstation)
  sudo apt-get install g++ libstdc++-7-dev
- Build the C extension
  make cbits/libcod.so

Workflow
========

- Compile
  stack build

- Repl is broken, but you can run it with
  stack exec coddle

- To run a file
  echo ":p 1+1" > script.cod
  stack exec coddle script.cod
