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

%.ll: %.cpp
	$(CPPC) -S -emit-llvm $<

%.bc: %.ll
	opt -o $@ $<

.PHONY: clean
clean:
	rm -rf build
	rm -f *.o *.ll *.o *.bc *.out
