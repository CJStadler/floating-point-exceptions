COMPILER := clang

trap_exceptions.so: examples/trap_exceptions.c
	${COMPILER} -lm -shared -fPIC -o $@ $<

overflow.out: examples/overflow.c
	${COMPILER} -o $@ $<

div_by_zero.out: examples/div_by_zero.c
	${COMPILER} -o $@ $<

inexact.out: examples/inexact.c
	${COMPILER} -o $@ $<

underflow.out: examples/underflow.c
	${COMPILER} -o $@ $<

invalid.out: examples/invalid.c
	${COMPILER} -o $@ $<
