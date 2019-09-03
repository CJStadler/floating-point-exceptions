COMPILER := clang

trap_exceptions.so: src/trap_exceptions.c
	${COMPILER} -lm -shared -fPIC -o $@ $<

overflow.out: src/overflow.c
	${COMPILER} -o $@ $<

div_by_zero.out: src/div_by_zero.c
	${COMPILER} -o $@ $<

inexact.out: src/inexact.c
	${COMPILER} -o $@ $<

underflow.out: src/underflow.c
	${COMPILER} -o $@ $<

invalid.out: src/invalid.c
	${COMPILER} -o $@ $<

.PHONY: clean
clean:
	rm *.out *.so
