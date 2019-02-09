coddle: *.hs
	ghc coddle.hs

test-scripts := $(wildcard tests/*.cd)

tests/%.out: tests/%.cd coddle
	./coddle $< > $@
	diff tests/$*.expected $@
	echo OK

test: tests/type-tests.out

clean-test-outputs:
	rm tests/*.out
