# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

dex := stack exec dex --

# --- building Dex ---

all: cbits/libdex.so
	stack build

# The web interface uses the Linux inotify service to detect changes to input
# files. On non-Linux you should compile without it.
all-no-web: cbits/libdex.so
	stack build --flag dex:-web

%.so: %.c
	gcc -fPIC -shared $^ -o $@

libdex: cbits/libdex.so

# --- running tets ---

example-names = type-tests eval-tests shadow-tests annot-tests flop-tests tutorial mandelbrot pi sierpinsky regression
quine-test-targets = $(example-names:%=run-%)
doc-names = $(example-names:%=doc/%.html)

tests: quine-tests quine-tests-interp stack-tests

quine-tests: $(quine-test-targets)

quine-tests-interp: runinterp-eval-tests runinterp-interp-tests

run-%: examples/%.dx
	misc/check-quine $^ $(dex) script --lit --allow-errors

runinterp-%: examples/%.dx
	misc/check-quine $^ $(dex) --interp script --lit --allow-errors

stack-tests:
	stack test

update-%: examples/%.dx
	$(dex) script --lit --allow-errors $^ > $^.tmp
	mv $^.tmp $^

# --- building docs ---

docs: doc/style.css $(doc-names)
	$(dex) --prelude /dev/null script prelude.dx --html > doc/prelude.html

doc/%.html: examples/%.dx
	$(dex) script $^ --html > $@

doc/%.css: static/%.css
	cp $^ $@
