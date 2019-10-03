COMPILER := clang
CLANG_FLAGS := -Xclang -disable-O0-optnone -ffast-math
OPT_FLAGS := -load build/report_exceptions/libReportExceptions.so -report_exceptions -instcombine

example.out: example.o
	$(COMPILER) -lm -o $@ $<

example.o: linked.bc
	llc --filetype=obj -o $@ $<

linked.bc: rtlib.bc example.bc
	llvm-link -o $@ $^

rtlib.bc: rtlib.ll
	opt -o $@ $<

example.bc: example-opt.ll
	opt -o $@ $<

rtlib.ll: rtlib.c
	$(COMPILER) -S -emit-llvm $<

example-opt.ll: example.ll build/report_exceptions/libReportExceptions.so
	opt -S $(OPT_FLAGS) -o $@ $<

example.ll: example.c
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) $<

build/report_exceptions/libReportExceptions.so: report_exceptions/ReportExceptions.cpp
	$(MAKE) -C build

.PHONY: clean
clean:
	rm -f *.o *.ll *.o *.bc *.out
