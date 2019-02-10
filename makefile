coddle: *.hs
	ghc coddle.hs

tests/%.out: tests/%.cd coddle
	./coddle $< > $@
	diff tests/$*.expected $@
	echo $* OK

test: tests/type-tests.out \
      tests/eval-tests.out
	rm $^
