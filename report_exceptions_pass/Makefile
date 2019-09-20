COMPILER := clang
OPT_FLAGS := -O1 -ffast-math

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

example-opt.ll: example.ll build/report_exceptions/libReportExceptions.so
	opt -S -load build/report_exceptions/libReportExceptions.so -report_exceptions -o $@ $<

example.ll: example.c
	$(COMPILER) -S -emit-llvm -g $(OPT_FLAGS) $<

build/report_exceptions/libReportExceptions.so: report_exceptions/ReportExceptions.cpp
	$(MAKE) -C build

.PHONY: clean
clean:
	rm -f *.o *.ll *.o *.bc *.out
