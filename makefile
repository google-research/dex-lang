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

	# Using separate stack-work directories to avoid recompiling when
	# changing between debug and non-debug builds, per
	# https://github.com/commercialhaskell/stack/issues/1132#issuecomment-386666166
	PROF := --profile --work-dir .stack-work-prof

	dex     := stack exec         dex --
	dexprof := stack exec $(PROF) dex --
endif


# --- building Dex ---

ifneq (,$(wildcard /usr/local/cuda/include/cuda.h))
STACK_FLAGS  = --flag dex:cuda
LIBDEX_FLAGS = -I/usr/local/cuda/include -lcuda -DDEX_CUDA
endif

.PHONY: all
all: build

# type-check only
tc:
	$(STACK) build --ghc-options -fno-code

build: libdex
	$(STACK) build $(STACK_FLAGS)

build-prof: libdex
	$(STACK) build $(PROF)

all-inotify: build-inotify

build-inotify: libdex
	$(STACK) build --flag dex:inotify $(PROF)

%.so: %.c
	gcc -std=c11 -fPIC -shared $^ $(LIBDEX_FLAGS) -o $@

libdex: cbits/libdex.so

# --- running tets ---

# TODO: re-enable linear-tests ad-tests include-test chol
example-names = uexpr-tests adt-tests type-tests eval-tests \
                shadow-tests monad-tests \
                ad-tests mandelbrot pi sierpinsky \
                regression brownian_motion particle-swarm-optimizer \
                ode-integrator parser-tests serialize-tests tiled-matmul \
                mcmc record-variant-tests simple-include-test ctc

quine-test-targets = $(example-names:%=run-%)

doc-names = $(example-names:%=doc/%.html)

tests: test-prep quine-tests repl-test

test-prep:
	rm -rf test-scratch/
	mkdir -p test-scratch/
	python3 misc/py/generate-dex-data.py

quine-tests: $(quine-test-targets)

quine-tests-interp: runinterp-eval-tests runinterp-ad-tests-interp runinterp-interp-tests

run-%: examples/%.dx build
	misc/check-quine $< $(dex) script --allow-errors

runinterp-%: examples/%.dx build
	misc/check-quine $< $(dex) --interp script --allow-errors

# Run these with profiling on while they're catching lots of crashes
prop-tests: cbits/libdex.so
	$(STACK) test $(PROF)

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

# --- building docs ---

slow-docs = doc/mnist-nearest-neighbors.html

docs: doc/style.css $(doc-names) $(slow-docs)
	$(dex) --prelude /dev/null script prelude.dx --html > doc/prelude.html

doc/%.html: examples/%.dx
	$(dex) script $^ --html > $@

doc/%.css: static/%.css
	cp $^ $@

benchmark:
	python benchmarks/numpy-bench.py 1000
	gcc -O3 -ffast-math benchmarks/cbench.c -o benchmarks/bench
	benchmarks/bench 1000
	$(dex) script benchmarks/time-tests.dx
	rm benchmarks/bench

clean:
	$(STACK) clean
