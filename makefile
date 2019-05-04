# Set shell to bash to resolve symbolic links when looking up
# executables, to support user-account installation of stack.
SHELL=/bin/bash

%.so: %.c
	gcc -fPIC -shared $^ -o $@

update-%: tests/%.cd
	stack exec coddle $< > tests/$*.expected

run-%: tests/%.cd
	stack exec coddle $< > tests/$*.out
	diff -u <(grep -vE '^$$' tests/$*.expected) \
	        <(grep -vE '^$$' tests/$*.out)
	echo $* OK

all-tests: run-type-tests run-eval-tests

all-update-tests: update-type-tests update-eval-tests

clean:
	rm cbits/*.so
