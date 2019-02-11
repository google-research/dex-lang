coddle: *.hs codlib.so
	ghc codlib.so coddle.hs

codlib.so: codlib.c
	gcc -fPIC -shared codlib.c -o codlib.so

tests/%.out: tests/%.cd coddle
	./coddle $< > $@
	diff tests/$*.expected $@
	echo $* OK

test: tests/type-tests.out \
      tests/eval-tests.out
	rm $^
