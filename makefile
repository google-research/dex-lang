# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

%.so: %.c
	gcc -fPIC -shared $^ -o $@

libcod: cbits/libcod.so

run-%: quine-tests/%.cd
	quine-tests/check-quine $^ stack exec coddle

update-%: tests/%.cd
	stack exec coddle $^ > $^.tmp
	mv $^.tmp $^

interp-test:
	./quine-tests/check-quine quine-tests/eval-tests.cd \
	stack exec coddle -- --interp

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
