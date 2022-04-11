# Main targets of interest for development
#
#   make tests             Run the full test suite in a clean build
#   make run-tests/<file>  Run one test file from tests/
#   make build             Build Dex (fastest complete compile time)
#   make watch             Build Dex continuously as source is edited
#   make check-watch       Just typecheck Dex continuously (fastest feedback)
#   make build-opt         Slower, but gives faster Dex compiles
#   make build-dbg         Slower, but better Haskell errors
#   make build-prof        Optimized for profiling the speed of the Dex compiler
#
# We suggest adding the following or equivalent aliases:
#
#   alias dex="stack exec dex -- --lib-path lib"
#   alias dexopt="stack exec --work-dir .stack-work-opt dex -- --lib-path lib"
#   alias dexdbg="stack exec --work-dir .stack-work-dbg --trace dex -- --lib-path lib"
#   alias dexprof="stack exec --work-dir .stack-work-prof --trace dex -- --lib-path lib"

# In more detail:
#
# - The default build is for quickly getting feedback on development
#   changes: get Haskell type errors and run small Dex test scripts as
#   fast as possible.
#
# - The opt build is for developing a Dex program or example (possibly
#   against a patched Dex): pay a slow optimizing compile once but have
#   the fastest possible Dex development loop.
#
# - The dbg build is for hunting (crash) bugs in Dex: pay slow GHC
#   compilation and slow Dex compilation, but get (relatively) detailed
#   stack traces from `error` and `C-c`, and extra internal debug checks.
#
# - The prof build is for profiling the Dex compiler: pay very slow GHC
#   compilation, but get relatively high signal-to-noise profiling
#   information on the Dex compiler's performance.
#
# The prof and dbg builds are different in two ways: prof turns on
# GHC's -O, but turns off Dex's self-checks and GHC's automatic cost
# center insertion.  This way (i) you're profiling optimized rather
# than unoptimized Dex, and (ii) the profile data is restricted to our
# {-# SCC #-} annotations, and thus not as overwhelming.
#
# We keep the builds in separate .stack-work directories so they don't
# step on each other's GHC-level compilation caches.
#
# The tests are run in the default `build` configuration, namely no
# optimization and no debug aids.


# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/usr/bin/env bash

STACK=$(shell command -v stack 2>/dev/null)
ifeq (, $(STACK))
	STACK=cabal

	DBG := --enable-library-profiling --enable-executable-profiling

	dex := cabal exec dex --
else
	STACK=stack

	PLATFORM := $(shell uname -s)
	ifeq ($(PLATFORM),Darwin)
		STACK=stack --stack-yaml=stack-macos.yaml
	endif

	DUMP_FLAGS = --ghc-options="-ddump-simpl" \
	             --ghc-options="-ddump-stg" \
	             --ghc-options="-dsuppress-all" \
	             --ghc-options="-dno-suppress-type-signatures" \
	             --ghc-options="-ddump-to-file"
	# Using separate stack-work directories to avoid recompiling when
	# changing between debug and non-debug builds, per
	# https://github.com/commercialhaskell/stack/issues/1132#issuecomment-386666166
	OPT  := --work-dir .stack-work-opt $(DUMP_FLAGS)
	DBG  := --work-dir .stack-work-dbg --trace
	PROF := --work-dir .stack-work-prof --trace --ghc-options="-fno-prof-auto" $(DUMP_FLAGS)

	dex := $(STACK) exec dex --
endif


# --- building Dex ---

CFLAGS := -fPIC

STACK_FLAGS := --ghc-options="-j +RTS -A256m -n2m -RTS"

# CUDA
ifneq (,$(wildcard /usr/local/cuda/include/cuda.h))
STACK_FLAGS := $(STACK_FLAGS) --flag dex:cuda
CFLAGS := $(CFLAGS) -I/usr/local/cuda/include -DDEX_CUDA
endif

# libpng
ifneq (,$(wildcard /usr/local/include/png.h))
CFLAGS := $(CFLAGS) -I/usr/local/include
endif

ifneq (,$(PREFIX))
STACK_BIN_PATH := --local-bin-path $(PREFIX)
endif

possible-clang-locations := clang++-9 clang++-10 clang++-11 clang++-12 clang++

CLANG := clang++

ifeq (1,$(DEX_LLVM_HEAD))
ifeq ($(PLATFORM),Darwin)
$(error LLVM head builds not supported on macOS!)
endif
STACK_FLAGS := $(STACK_FLAGS) --flag dex:llvm-head
STACK := $(STACK) --stack-yaml=stack-llvm-head.yaml
else
CLANG := $(shell for clangversion in $(possible-clang-locations) ; do \
if [[ $$(command -v "$$clangversion" 2>/dev/null) ]]; \
then echo "$$clangversion" ; break ; fi ; done)
ifeq (,$(CLANG))
$(error "Please install clang++-12")
endif
clang-version-compatible := $(shell $(CLANG) -dumpversion | awk '{ print(gsub(/^((9\.)|(10\.)|(11\.)|(12\.)).*$$/, "")) }')
ifneq (1,$(clang-version-compatible))
$(error "Please install clang++-12")
endif
endif

CXXFLAGS := $(CFLAGS) -std=c++11 -fno-exceptions -fno-rtti
CFLAGS := $(CFLAGS) -std=c11

.PHONY: all
all: build

# type-check only
tc: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --ghc-options -fno-code

# Build without clearing the cache. Use at your own risk.
just-build: dexrt-llvm
	$(STACK) build $(STACK_FLAGS)

build: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --fast
	$(dex) clean             # clear cache
	$(dex) script /dev/null  # precompile the prelude

watch: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --fast --file-watch

check-watch: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --fast --file-watch --ghc-options="-fno-code"

install: dexrt-llvm
	$(STACK) install $(STACK_BIN_PATH) --flag dex:optimized $(STACK_FLAGS)

build-opt: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(OPT) --flag dex:optimized

build-dbg: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(DBG) --flag dex:debug

build-prof: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(PROF) --flag dex:optimized

# For some reason stack fails to detect modifications to foreign library files
build-ffis: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --force-dirty --flag dex:foreign
	$(eval STACK_INSTALL_DIR=$(shell $(STACK) path --local-install-root))
	cp $(STACK_INSTALL_DIR)/lib/libDex.so python/dex/
	cp $(STACK_INSTALL_DIR)/lib/libDex.so julia/deps/

build-ci: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --force-dirty --ghc-options "-Werror -fforce-recomp"
	$(dex) clean             # clear cache
	$(dex) script /dev/null  # precompile the prelude

build-nolive: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --flag dex:-live

dexrt-llvm: src/lib/dexrt.bc

%.bc: %.cpp
	$(CLANG) $(CXXFLAGS) -DDEX_LIVE -c -emit-llvm $^ -o $@

# --- running tests ---

example-names = mandelbrot pi sierpinski rejection-sampler \
                regression brownian_motion particle-swarm-optimizer \
                ode-integrator mcmc ctc raytrace particle-filter \
                isomorphisms ode-integrator fluidsim \
                sgd psd kernelregression \
                quaternions manifold-gradients schrodinger tutorial \
                latex
# TODO: re-enable
# fft vega-plotting

test-names = uexpr-tests adt-tests type-tests eval-tests show-tests \
             shadow-tests monad-tests io-tests exception-tests sort-tests \
             ad-tests parser-tests serialize-tests parser-combinator-tests \
             record-variant-tests typeclass-tests complex-tests trig-tests \
             linalg-tests set-tests

lib-names = diagram plot png

all-names = $(test-names:%=tests/%) $(example-names:%=examples/%)

quine-test-targets = $(all-names:%=run-%)

update-test-targets    = $(test-names:%=update-tests/%)
update-example-targets = $(example-names:%=update-examples/%)

doc-example-names = $(example-names:%=doc/examples/%.html)

doc-lib-names = $(lib-names:%=doc/lib/%.html)

tests: unit-tests quine-tests repl-test module-tests

unit-tests:
	$(STACK) test $(STACK_FLAGS)

quine-tests: $(quine-test-targets)

run-%: export DEX_ALLOW_CONTRACTIONS=0
run-%: export DEX_TEST_MODE=t

run-tests/%: tests/%.dx just-build
	misc/check-quine $< $(dex) script --allow-errors
run-examples/%: examples/%.dx just-build
	misc/check-quine $< $(dex) script --allow-errors

update-%: export DEX_ALLOW_CONTRACTIONS=0
update-%: export DEX_TEST_MODE=t

update-all: $(update-test-targets) $(update-example-targets)

update-tests/%: tests/%.dx just-build
	$(dex) script --allow-errors $< > $<.tmp
	mv $<.tmp $<

update-examples/%: examples/%.dx just-build
	$(dex) script --allow-errors $< > $<.tmp
	mv $<.tmp $<

run-gpu-tests: export DEX_ALLOC_CONTRACTIONS=0
run-gpu-tests: tests/gpu-tests.dx just-build
	misc/check-quine $< $(dex) --backend llvm-cuda script --allow-errors

update-gpu-tests: export DEX_ALLOW_CONTRACTIONS=0
update-gpu-tests: tests/gpu-tests.dx just-build
	$(dex) --backend llvm-cuda script --allow-errors $< > $<.tmp
	mv $<.tmp $<

repl-test: just-build
	misc/check-no-diff \
	  tests/repl-multiline-test-expected-output \
	  <($(dex) repl < tests/repl-multiline-test.dx)

module-tests: just-build
	misc/check-quine tests/module-tests.dx \
    $(dex) --prelude lib/prelude.dx --lib-path tests script --allow-errors

# --- running and querying benchmarks ---

bench-summary:
	sqlite3 results.db < benchmarks/queries/result-summary.sql

# bench-set-standard:
# 	python3 dexbench.py adhoc --name standard

# bench-compare:
# 	python3 dexbench.py adhoc --name proposed
# 	cat <(  echo ".parameter set :old_version standard" \
#              && echo ".parameter set :new_version proposed" \
#              && cat queries/compare-versions.sql )          \
#           | sqlite3 bench_results.db

# --- building docs ---

slow-docs = doc/examples/mnist-nearest-neighbors.html

docs: doc-prelude $(doc-example-names) $(doc-lib-names) $(slow-docs)

doc-prelude: lib/prelude.dx
	mkdir -p doc
	$(dex) --prelude /dev/null script lib/prelude.dx --outfmt html > doc/prelude.html

doc/examples/%.html: examples/%.dx
	mkdir -p doc/examples
	$(dex) script $^ --outfmt html > $@

doc/lib/%.html: lib/%.dx
	mkdir -p doc/lib
	$(dex) script $^ --outfmt html > $@

clean:
	$(STACK) clean
	rm -rf src/lib/dexrt.bc
