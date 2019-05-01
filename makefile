SHELL=/bin/bash

%.so: %.c
	gcc -fPIC -shared $^ -o $@

update-%:
	./coddle tests/$*.cd > tests/$*.expected

run-%: tests/%.cd
	stack exec coddle $< > tests/$*.out
	diff tests/$*.expected tests/$*.out
	echo $* OK

all-tests: run-type-tests run-eval-tests

all-update-tests: update-type-tests update-eval-tests

clean:
	rm *.hi *.o *.so

hs-packages:
	cabal install lens QuickCheck tf-random llvm-hs lens hinotify \
	aeson megaparsec warp optparse-applicative
