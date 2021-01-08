# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

STACK=$(shell command -v stack 2>/dev/null)
ifeq (, $(STACK))
	STACK=cabal

	PROF := --enable-library-profiling --enable-executable-profiling

	dex     := cabal exec dex --
	dexprof := cabal exec $(PROF) dex -- +RTS -p -RTS
else
	STACK=stack

	PLATFORM := $(shell uname -s)
	ifeq ($(PLATFORM),Darwin)
		STACK=stack --stack-yaml=stack-macos.yaml
	endif

	# Using separate stack-work directories to avoid recompiling when
	# changing between debug and non-debug builds, per
	# https://github.com/commercialhaskell/stack/issues/1132#issuecomment-386666166
	PROF := --profile --work-dir .stack-work-prof

	dex     := $(STACK) exec         dex --
	dexprof := $(STACK) exec $(PROF) dex --
endif


# --- building Dex ---

CFLAGS := -fPIC

# CUDA
ifneq (,$(wildcard /usr/local/cuda/include/cuda.h))
STACK_FLAGS = --flag dex:cuda
CFLAGS := $(CFLAGS) -I/usr/local/cuda/include -DDEX_CUDA
endif

# libpng
ifneq (,$(wildcard /usr/local/include/png.h))
CFLAGS := $(CFLAGS) -I/usr/local/include
endif

ifneq (,$(PREFIX))
STACK_BIN_PATH := --local-bin-path $(PREFIX)
endif

CXXFLAGS := $(CFLAGS) -std=c++11 -fno-exceptions -fno-rtti
CFLAGS := $(CFLAGS) -std=c11

.PHONY: all
all: build

# type-check only
tc: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --ghc-options -fno-code

build: dexrt-llvm
	$(STACK) build $(STACK_FLAGS)

watch: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --file-watch

install: dexrt-llvm
	$(STACK) install $(STACK_BIN_PATH) --flag dex:optimized $(STACK_FLAGS)

build-prof: dexrt-llvm
	$(STACK) build $(PROF)

# For some reason stack fails to detect modifications to foreign library files
build-python: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --force-dirty
	$(eval STACK_INSTALL_DIR=$(shell stack path --local-install-root))
	cp $(STACK_INSTALL_DIR)/lib/libDex.so python/dex/

build-ci: dexrt-llvm
	$(STACK) build $(STACK_FLAGS) --force-dirty --ghc-options "-Werror -fforce-recomp"

dexrt-llvm: src/lib/dexrt.bc

%.bc: %.cpp
	clang++ $(CXXFLAGS) -c -emit-llvm $^ -o $@

# --- running tests ---

example-names = mandelbrot pi sierpinski rejection-sampler \
                regression brownian_motion particle-swarm-optimizer \
                ode-integrator mcmc ctc raytrace particle-filter \
                isomorphisms ode-integrator linear_algebra fluidsim \
                sgd chol

test-names = uexpr-tests adt-tests type-tests eval-tests show-tests \
             shadow-tests monad-tests io-tests exception-tests \
             ad-tests parser-tests serialize-tests parser-combinator-tests \
             record-variant-tests typeclass-tests complex-tests trig-tests

lib-names = diagram plot png

all-names = $(test-names:%=tests/%) $(example-names:%=examples/%)

quine-test-targets = $(all-names:%=run-%)

update-test-targets    = $(test-names:%=update-tests-%)
update-example-targets = $(example-names:%=update-examples-%)

doc-example-names = $(example-names:%=doc/examples/%.html)

doc-lib-names = $(lib-names:%=doc/lib/%.html)

tests: quine-tests repl-test

quine-tests: $(quine-test-targets)

run-%: export DEX_ALLOW_CONTRACTIONS=0
run-%: export DEX_TEST_MODE=t

run-tests/%: tests/%.dx build
	misc/check-quine $< $(dex) script --allow-errors
run-examples/%: examples/%.dx build
	misc/check-quine $< $(dex) script --allow-errors

# Run these with profiling on while they're catching lots of crashes
prop-tests: cbits/libdex.so
	$(STACK) test $(PROF)

update-%: export DEX_ALLOW_CONTRACTIONS=0
update-%: export DEX_TEST_MODE=t

update-all: $(update-test-targets) $(update-example-targets)

update-tests-%: tests/%.dx build
	$(dex) script --allow-errors $< > $<.tmp
	mv $<.tmp $<

update-examples-%: examples/%.dx build
	$(dex) script --allow-errors $< > $<.tmp
	mv $<.tmp $<

run-gpu-tests: export DEX_ALLOC_CONTRACTIONS=0
run-gpu-tests: tests/gpu-tests.dx build
	misc/check-quine $< $(dex) --backend llvm-cuda script --allow-errors

update-gpu-tests: export DEX_ALLOW_CONTRACTIONS=0
update-gpu-tests: tests/gpu-tests.dx build
	$(dex) --backend llvm-cuda script --allow-errors $< > $<.tmp
	mv $<.tmp $<

uexpr-tests:
	misc/check-quine examples/uexpr-tests.dx $(dex) script

repl-test:
	misc/check-no-diff \
	  tests/repl-multiline-test-expected-output \
	  <($(dex) repl < tests/repl-multiline-test.dx)

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
