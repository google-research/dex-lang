# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

dex := stack exec dex --

# --- building Dex ---

all: cbits/libdex.so
	stack build

all-inotify: cbits/libdex.so
	stack build --flag dex:inotify

%.so: %.c
	gcc -fPIC -shared $^ -o $@

libdex: cbits/libdex.so

# --- running tets ---

example-names = type-tests linear-tests eval-tests ad-tests shadow-tests annot-tests \
                flop-tests tutorial mandelbrot pi sierpinsky \
                regression brownian_motion
quine-test-targets = $(example-names:%=run-%)
doc-names = $(example-names:%=doc/%.html)

tests: quine-tests quine-tests-interp repl-test

quine-tests: $(quine-test-targets)

quine-tests-interp: runinterp-eval-tests runinterp-ad-tests-interp runinterp-interp-tests

run-%: examples/%.dx
	misc/check-quine $^ $(dex) script --lit --allow-errors

runinterp-%: examples/%.dx
	misc/check-quine $^ $(dex) --interp script --lit --allow-errors

prop-tests: cbits/libdex.so
	stack test

update-%: examples/%.dx
	$(dex) script --lit --allow-errors $^ > $^.tmp
	mv $^.tmp $^

repl-test:
	misc/check-no-diff \
	  examples/repl-multiline-test-expected-output \
	  <($(dex) repl < examples/repl-multiline-test.dx)

# --- building docs ---

docs: doc/style.css $(doc-names)
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
