coddle: *.hs codlib.so
	ghc codlib.so coddle.hs

codlib.so: codlib.c
	gcc -fPIC -shared codlib.c -o codlib.so

%: tests/%.cd coddle
	./coddle $< > tests/$*.out
	diff tests/$*.expected tests/$*.out
	echo $* OK

tests: type-tests eval-tests
