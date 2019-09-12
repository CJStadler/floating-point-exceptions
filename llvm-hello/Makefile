example.out: example.o
	clang -o $@ $<

example.o: linked.bc
	llc-8 --filetype=obj -o $@ $<

linked.bc: rtlib.bc example.bc
	llvm-link-8 -o $@ $^

rtlib.bc: rtlib.ll
	opt -o $@ $<

example.bc: example-opt.ll
	opt -o $@ $<

rtlib.ll: rtlib.c
	clang -S -emit-llvm $<

example-opt.ll: example.ll build/hello/libHello.so
	opt -load build/hello/libHello.so -hello -o $@ $<

example.ll: example.c
	clang -S -emit-llvm -g -O1 -ffast-math $<

build/hello/libHello.so: hello/Hello.cpp
	$(MAKE) -C build

.PHONY: clean
clean:
	rm *.o *.ll *.o *.bc *.out
