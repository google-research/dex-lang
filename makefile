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

# Make sure we always use a debug build in CI --- it enables extra checks!
ifneq (,$(DEX_CI))
STACK_FLAGS := $(STACK_FLAGS) --flag dex:debug
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

CXXFLAGS := $(CFLAGS) -std=c++11 -fno-exceptions -fno-rtti -pthread
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
	$(STACK) install $(STACK_BIN_PATH) --flag dex:optimized $(STACK_FLAGS) $(OPT)

build-opt: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(OPT) --flag dex:optimized

build-dbg: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(DBG) --flag dex:debug

build-prof: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) $(PROF) --flag dex:optimized

# For some reason stack fails to detect modifications to foreign library files
build-ffis: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --work-dir .stack-work-ffis --force-dirty --flag dex:foreign --flag dex:optimized
	$(eval STACK_INSTALL_DIR=$(shell $(STACK) path --work-dir .stack-work-ffis --local-install-root))
	cp $(STACK_INSTALL_DIR)/lib/libDex.so python/dex/
	cp $(STACK_INSTALL_DIR)/lib/libDex.so julia/deps/

# This target is for CI, because it wants to be able to both run the
# `dex` executable and load the `dex` Python package from the same
# directory, without a needless recompile.
build-ffis-and-exe: dexrt-llvm
	$(STACK) build   $(STACK_FLAGS) --work-dir .stack-work-ffis \
	 --flag dex:foreign --flag dex:optimized --force-dirty
	$(STACK) install $(STACK_FLAGS) --work-dir .stack-work-ffis \
	 --flag dex:foreign --flag dex:optimized --local-bin-path .
	$(eval STACK_INSTALL_DIR=$(shell $(STACK) path --work-dir .stack-work-ffis --local-install-root))
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

example-names := \
  mandelbrot pi sierpinski rejection-sampler \
  regression brownian_motion particle-swarm-optimizer \
  ode-integrator mcmc ctc raytrace particle-filter \
  isomorphisms fluidsim \
  sgd psd kernelregression nn \
  quaternions manifold-gradients schrodinger tutorial \
  latex linear-maps dither mcts md
# TODO: re-enable
# fft vega-plotting

# Only test levenshtein-distance on Linux, because MacOS ships with a
# different (apparently _very_ different) word list.
ifeq ($(shell uname -s),Linux)
  example-names += levenshtein-distance
endif

test-names = uexpr-tests print-tests adt-tests type-tests struct-tests cast-tests eval-tests show-tests \
             read-tests shadow-tests monad-tests io-tests exception-tests sort-tests \
             standalone-function-tests \
             ad-tests parser-tests serialize-tests parser-combinator-tests \
             record-variant-tests typeclass-tests complex-tests trig-tests \
             linalg-tests set-tests fft-tests stats-tests stack-tests

doc-names = conditionals functions

lib-names = complex fft netpbm plot sort diagram linalg parser png set stats

benchmark-names = \
  fused_sum gaussian jvp_matmul matmul_big matmul_small matvec_big matvec_small \
  poly vjp_matmul

quine-test-targets = \
  $(test-names:%=run-tests/%) \
  $(example-names:%=run-examples/%) \
  $(doc-names:%=run-doc/%) \
  $(lib-names:%=run-lib/%) \
  $(benchmark-names:%=run-bench-tests/%)

update-test-targets    = $(test-names:%=update-tests/%)
update-doc-targets     = $(doc-names:%=update-doc/%)
update-lib-targets     = $(lib-names:%=update-lib/%)
update-example-targets = $(example-names:%=update-examples/%)

t10k-images-idx3-ubyte-sha256 = 346e55b948d973a97e58d2351dde16a484bd415d4595297633bb08f03db6a073
t10k-labels-idx1-ubyte-sha256 = 67da17c76eaffca5446c3361aaab5c3cd6d1c2608764d35dfb1850b086bf8dd5

tutorial-data = t10k-images-idx3-ubyte t10k-labels-idx1-ubyte
tutorial-data := $(tutorial-data:%=examples/%)

$(tutorial-data):
	wget -qO $@.gz http://fashion-mnist.s3-website.eu-central-1.amazonaws.com/$(@F).gz
	@echo $($(@F)-sha256) $@.gz > $@.sha256
	sha256sum -c $@.sha256
	$(RM) $@.sha256
	gunzip $@.gz

.PHONY: tutorial-data
tutorial-data: $(tutorial-data)

run-examples/tutorial: tutorial-data
update-examples/tutorial: tutorial-data

camera-sha256 = c5c69e1bf02f219b6e1c12c13405671425aa1c4dc130c1c380e7416a064341bc
dither-data = camera
dither-data := $(dither-data:%=examples/%)

$(dither-data):
	wget -qO $@.ppm https://gist.github.com/niklasschmitz/03be29c2850ac3bbdf6ce86229b71d8f/raw/300962b117fe8595913fb1f35db546b53974576c/$(@F).ppm
	@echo $($(@F)-sha256) $@.ppm > $@.sha256
	sha256sum -c $@.sha256
	$(RM) $@.sha256

.PHONY: dither-data
dither-data: $(dither-data)
run-examples/dither: dither-data
update-examples/dither: dither-data

tests: opt-tests unit-tests lower-tests quine-tests repl-test module-tests doc-format-test file-check-tests

# Keep the unit tests in their own working directory too, due to
# https://github.com/commercialhaskell/stack/issues/4977
unit-tests:
	$(STACK) test --work-dir .stack-work-test $(STACK_FLAGS)

watch-unit-tests:
	$(STACK) test --work-dir .stack-work-test $(STACK_FLAGS) --file-watch

unit-tests-dbg:
	$(STACK) test --work-dir .stack-work-test-dbg --trace $(STACK_FLAGS)

opt-tests: just-build
	misc/file-check tests/opt-tests.dx $(dex) -O script
	misc/file-check tests/inline-tests.dx $(dex) -O script

doc-format-test: $(doc-files) $(example-files) $(lib-files)
	python3 misc/build-web-index "$(doc-files)" "$(example-files)" "$(lib-files)" > /dev/null

quine-tests: $(quine-test-targets)

file-check-tests: just-build
	misc/file-check tests/instance-interface-syntax-tests.dx $(dex) -O script

run-%: export DEX_ALLOW_CONTRACTIONS=0
run-%: export DEX_TEST_MODE=t

run-tests/%: tests/%.dx just-build
	misc/check-quine $< $(dex) -O script
run-doc/%: doc/%.dx just-build
	misc/check-quine $< $(dex) script
run-lib/%: lib/%.dx just-build
	misc/check-quine $< $(dex) script
run-examples/%: examples/%.dx just-build
	misc/check-quine $< $(dex) -O script
# This runs the benchmark in test mode, which means we're checking
# that it's not broken, but not actually trying to measure runtimes
run-bench-tests/%: benchmarks/%.dx just-build
	misc/check-quine $< $(dex) -O script

lower-tests: export DEX_LOWER=1
lower-tests: export DEX_ALLOW_CONTRACTIONS=0
lower-tests: export DEX_TEST_MODE=t
lower-tests: just-build
	misc/check-quine tests/lower.dx $(dex) script
update-lower-tests: just-build
	$(dex) script tests/lower.dx > tests/lower.dx.tmp
	mv tests/lower.dx.tmp tests/lower.dx

lower-vectorize-tests: export DEX_LOWER=1
lower-vectorize-tests: export DEX_VECTORIZE=1
lower-vectorize-tests: export DEX_ALLOW_CONTRACTIONS=0
lower-vectorize-tests: export DEX_TEST_MODE=t
lower-vectorize-tests: just-build
	misc/check-quine tests/lower-vectorize.dx $(dex) script
update-lower-vectorize-tests: just-build
	DEX_LOWER=1 DEX_VECTORIZE=1 $(dex) script tests/lower-vectorize.dx > tests/lower-vectorize.dx.tmp
	mv tests/lower-vectorize.dx.tmp tests/lower-vectorize.dx

update-%: export DEX_ALLOW_CONTRACTIONS=0
update-%: export DEX_TEST_MODE=t

update-all: $(update-test-targets) $(update-doc-targets) $(update-lib-targets) $(update-example-targets)

update-tests/%: tests/%.dx just-build
	$(dex) script $< > $<.tmp
	mv $<.tmp $<

update-doc/%: doc/%.dx just-build
	$(dex) script $< > $<.tmp
	mv $<.tmp $<

update-lib/%: lib/%.dx just-build
	$(dex) script $< > $<.tmp
	mv $<.tmp $<

update-examples/%: examples/%.dx just-build
	$(dex) script $< > $<.tmp
	mv $<.tmp $<

update-bench-tests/%: benchmarks/%.dx just-build
	$(dex) script $< > $<.tmp
	mv $<.tmp $<

run-gpu-tests: export DEX_ALLOW_CONTRACTIONS=0
run-gpu-tests: tests/gpu-tests.dx just-build
	misc/check-quine $< $(dex) --backend llvm-cuda script

update-gpu-tests: export DEX_ALLOW_CONTRACTIONS=0
update-gpu-tests: tests/gpu-tests.dx just-build
	$(dex) --backend llvm-cuda script $< > $<.tmp
	mv $<.tmp $<

repl-test: just-build
	misc/check-no-diff \
	  tests/repl-multiline-test-expected-output \
	  <($(dex) repl < tests/repl-multiline-test.dx)
	misc/check-no-diff \
	  tests/repl-regression-528-test-expected-output \
	  <($(dex) repl < tests/repl-regression-528-test.dx)

module-tests: just-build
	misc/check-quine tests/module-tests.dx \
    $(dex) --prelude lib/prelude.dx --lib-path tests script

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

slow-pages = pages/examples/mnist-nearest-neighbors.html

doc-files = $(doc-names:%=doc/%.dx)
pages-doc-files = $(doc-names:%=pages/%.html)
example-files = $(example-names:%=examples/%.dx)
pages-example-files = $(example-names:%=pages/examples/%.html)

lib-files = $(filter-out lib/prelude.dx,$(wildcard lib/*.dx))
pages-lib-files = $(patsubst %.dx,pages/%.html,$(lib-files))

docs: pages-prelude $(pages-doc-files) $(pages-example-files) $(pages-lib-files) $(slow-pages) pages/index.md

pages-prelude: lib/prelude.dx
	mkdir -p pages
	$(dex) --prelude /dev/null script lib/prelude.dx --outfmt html > pages/prelude.html

pages/examples/tutorial.html: tutorial-data
pages/examples/dither.html: dither-data

pages/examples/%.html: examples/%.dx
	mkdir -p pages/examples
	$(dex) script $< --outfmt html > $@

pages/lib/%.html: lib/%.dx
	mkdir -p pages/lib
	$(dex) script $^ --outfmt html > $@

pages/index.md: $(doc-files) $(example-files) $(lib-files)
	python3 misc/build-web-index "$(doc-files)" "$(example-files)" "$(lib-files)" > $@

${pages-doc-files}:pages/%.html: doc/%.dx
	mkdir -p pages
	$(dex) script $^ --outfmt html > $@

clean:
	$(STACK) clean
	$(RM) src/lib/dexrt.bc
	$(RM) $(tutorial-data)
	$(RM) $(dither-data)
