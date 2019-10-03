# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

# Build Dex
all: cbits/libdex.so
	stack build


# Dex uses the Linux inotify service to detect changes to input files.
# This is only used in the web interface, so on non-Linux you can
# compile without it
all-no-web: cbits/libdex.so
	stack build --flag dex:-web

# Run all tests. T
tests: interp-test \
       run-type-tests \
       run-eval-tests \
       run-shadow-tests \
       run-annot-tests \
       run-flop-tests \
       run-tutorial \
       run-mandelbrot \
       stack-tests

%.so: %.c
	gcc -fPIC -shared $^ -o $@

libdex: cbits/libdex.so

run-%: examples/%.dx
	misc/check-quine $^ \
	stack exec dex -- script --lit --allow-errors

update-%: tests/%.dx
	stack exec dex $^ > $^.tmp
	mv $^.tmp $^

interp-test:
	./misc/check-quine examples/eval-tests.dx \
	stack exec dex -- --interp script --lit --allow-errors

stack-tests:
	stack test

doc/%.html: examples/%.dx
	stack exec dex -- script $^ --html > $@

docs: doc/mandelbrot.html \
      doc/tutorial.html
	cp static/style.css doc
	cp static/plot.js doc

clean-docs:
	rm doc/*
