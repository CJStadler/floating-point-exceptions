COMPILER := clang
OPT_FLAGS := # -O1 -ffast-math

example.out: example.o
	$(COMPILER) -lm -o $@ $<

example.o: linked.bc
	llc-8 --filetype=obj -o $@ $<

linked.bc: rtlib.bc example.bc
	llvm-link-8 -o $@ $^

rtlib.bc: rtlib.ll
	opt -o $@ $<

example.bc: example-opt.ll
	opt -o $@ $<

rtlib.ll: rtlib.c
	$(COMPILER) -S -emit-llvm $<

example-opt.ll: example.ll build/hello/libHello.so
	opt -load build/hello/libHello.so -hello -o $@ $<

example.ll: example.c
	$(COMPILER) -S -emit-llvm -g $(OPT_FLAGS) $<

build/hello/libHello.so: hello/Hello.cpp
	$(MAKE) -C build

.PHONY: clean
clean:
	rm *.o *.ll *.o *.bc *.out
