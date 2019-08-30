COMPILER := clang

trap_exceptions.so: examples/trap_exceptions.c
	${COMPILER} -lm -shared -fPIC -o $@ $<

overflow.out: examples/overflow.c
	${COMPILER} -o $@ $<
