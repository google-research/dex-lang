# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

%.so: %.c
	gcc -fPIC -shared $^ -o $@

libdex: cbits/libdex.so

run-%: quine-tests/%.dx
	quine-tests/check-quine $^ \
	stack exec dex -- script --lit --allow-errors

update-%: tests/%.dx
	stack exec dex $^ > $^.tmp
	mv $^.tmp $^

interp-test:
	./quine-tests/check-quine quine-tests/eval-tests.dx \
	stack exec dex -- --interp script --lit --allow-errors

stack-tests:
	stack test

all-tests: interp-test \
           run-type-tests \
           run-eval-tests \
           run-shadow-tests \
           run-annot-tests \
           run-flop-tests \
           stack-tests

clean:
	rm cbits/*.so
