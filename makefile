coddle: *.hs codlib.so
	ghc codlib.so coddle.hs

codlib.so: codlib.c
	gcc -fPIC -shared codlib.c -o codlib.so

update-%:
	./coddle tests/$*.cd > tests/$*.expected

run-%: tests/%.cd coddle
	./coddle $< > tests/$*.out
	diff tests/$*.expected tests/$*.out
	echo $* OK

all-tests: run-type-tests run-eval-tests

all-update-tests: update-type-tests update-eval-tests

clean:
	rm *.hi *.o *.so

hs-packages:
	cabal install lens QuickCheck tf-random llvm-hs lens hinotify \
	aeson megaparsec warp optparse-applicative
