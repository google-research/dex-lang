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

ifneq (,$(wildcard /usr/local/cuda/include/cuda.h))
STACK_FLAGS = --flag dex:cuda
CFLAGS := $(CFLAGS) -I/usr/local/cuda/include -DDEX_CUDA
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

build-prof: dexrt-llvm
	$(STACK) build $(PROF)

dexrt-llvm: src/lib/dexrt.bc

# For some reason stack fails to detect modifications to foreign library files
build-python: build
	$(STACK) build $(STACK_FLAGS) --force-dirty
	$(eval STACK_INSTALL_DIR=$(shell stack path --local-install-root))
	cp $(STACK_INSTALL_DIR)/lib/libDex.so python/dex/

%.bc: %.cpp
	clang++ $(CXXFLAGS) -c -emit-llvm $^ -o $@

# --- running tets ---

# TODO: re-enable linear-tests ad-tests include-test chol
example-names = uexpr-tests adt-tests type-tests eval-tests \
                shadow-tests monad-tests \
                ad-tests mandelbrot pi sierpinsky \
                regression brownian_motion particle-swarm-optimizer \
                ode-integrator parser-tests serialize-tests \
                mcmc record-variant-tests simple-include-test ctc raytrace

quine-test-targets = $(example-names:%=run-%)

doc-names = $(example-names:%=doc/%.html)

tests: test-prep quine-tests repl-test

test-prep:
	rm -rf test-scratch/
	mkdir -p test-scratch/
	python3 misc/py/generate-dex-data.py

quine-tests: $(quine-test-targets)

quine-tests-interp: runinterp-eval-tests runinterp-ad-tests-interp runinterp-interp-tests

run-%: export DEX_ALLOW_CONTRACTIONS=0
run-%: examples/%.dx build
	misc/check-quine $< $(dex) script --allow-errors

# Run these with profiling on while they're catching lots of crashes
prop-tests: cbits/libdex.so
	$(STACK) test $(PROF)

update-%: export DEX_ALLOW_CONTRACTIONS=0
update-%: examples/%.dx build
	$(dex) script --allow-errors $< > $<.tmp
	mv $<.tmp $<

jax-tests: build
	misc/check-quine examples/jax-tests.dx $(dex) --backend JAX script

uexpr-tests:
	misc/check-quine examples/uexpr-tests.dx $(dex) script

repl-test:
	misc/check-no-diff \
	  examples/repl-multiline-test-expected-output \
	  <($(dex) repl < examples/repl-multiline-test.dx)

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

slow-docs = doc/mnist-nearest-neighbors.html

docs: doc/style.css $(doc-names) $(slow-docs)
	$(dex) --prelude /dev/null script prelude.dx --html > doc/prelude.html

doc/%.html: examples/%.dx
	$(dex) script $^ --outfmt HTML > $@

doc/%.css: static/%.css
	cp $^ $@

clean:
	$(STACK) clean
	rm -rf src/lib/dexrt.bc
