CC := clang
CPPC := clang++
CLANG_FLAGS := -Xclang -disable-O0-optnone -ffast-math
OPT_FLAGS := -load build/report_exceptions/libReportExceptions.so -report_exceptions -instcombine

all: build/report_exceptions/libReportExceptions.so rtlib.bc fp_exception.bc

build/report_exceptions/libReportExceptions.so: build report_exceptions/ReportExceptions.cpp
	$(MAKE) -C build

build:
	mkdir build
	cd build; cmake ..

example.out: example.o
	$(CPPC) -lm -o $@ $<

example.o: linked.bc
	llc --filetype=obj -o $@ $<

linked.bc: rtlib.bc example.bc fp_exception.bc
	llvm-link -o $@ $^

example.bc: example-opt.ll
	opt -o $@ $<

example-opt.ll: example.ll # build/report_exceptions/libReportExceptions.so
	opt -S $(OPT_FLAGS) -o $@ $<

example.ll: example.c
	$(CC) -S -emit-llvm -g $(CLANG_FLAGS) $<

%.ll: %.cpp
	$(CPPC) -S -emit-llvm $<

%.bc: %.ll
	opt -o $@ $<

.PHONY: clean
clean:
	rm -rf build
	rm -f *.o *.ll *.o *.bc *.out
