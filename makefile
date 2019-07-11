# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

%.so: %.c
	gcc -fPIC -shared $^ -o $@

run-%: tests/%.cd
	./check-quine $^ stack exec coddle

update-%: tests/%.cd
	stack exec coddle $^ > $^.tmp
	mv $^.tmp $^

all-tests: run-type-tests \
           run-eval-tests \
           run-shadow-tests \
           run-annot-tests \
           run-flop-tests \
           # run-ad-tests

clean:
	rm cbits/*.so
