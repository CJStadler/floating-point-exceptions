COMPILER := clang
FLAGS := -O0

trap_exceptions.so: src/trap_exceptions.c
	${COMPILER} -lm -shared -fPIC -o $@ $<

overflow.out: src/overflow.c
	${COMPILER} ${FLAGS} -o $@ $<

div_by_zero.out: src/div_by_zero.c
	${COMPILER} ${FLAGS} -o $@ $<

inexact.out: src/inexact.c
	${COMPILER} ${FLAGS} -o $@ $<

underflow.out: src/underflow.c
	${COMPILER} ${FLAGS} -o $@ $<

invalid.out: src/invalid.c
	${COMPILER} ${FLAGS} -o $@ $<

.PHONY: clean
clean:
	rm *.out *.so
