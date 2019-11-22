CC := clang
CPPC := clang++
CLANG_FLAGS := -Xclang -disable-O0-optnone -ffast-math
OPT_FLAGS := -load build/report_exceptions/libReportExceptions.so -report_exceptions -instcombine

build/report_exceptions/libReportExceptions.so: report_exceptions/ReportExceptions.cpp
	$(MAKE) -C build

rtlib.bc: rtlib.ll
	opt -o $@ $<

rtlib.ll: rtlib.cpp
	$(CPPC) -S -emit-llvm $<

example.out: example.o
	$(CC) -lm -o $@ $<

example.o: linked.bc
	llc --filetype=obj -o $@ $<

linked.bc: rtlib.bc example.bc
	llvm-link -o $@ $^

example.bc: example-opt.ll
	opt -o $@ $<

example-opt.ll: example.ll build/report_exceptions/libReportExceptions.so
	opt -S $(OPT_FLAGS) -o $@ $<

example.ll: example.c
	$(CC) -S -emit-llvm -g $(CLANG_FLAGS) $<

.PHONY: clean
clean:
	rm -f *.o *.ll *.o *.bc *.out
