COMPILER := clang++
PASS_LIB := ../report_exceptions_pass/build/report_exceptions/libReportExceptions.so
RTLIB := ../report_exceptions_pass/rtlib.bc
CLANG_FLAGS := # -Xclang -disable-O0-optnone -ffast-math
LLVM_FLAGS := -load $(PASS_LIB) -report_exceptions

turbine1_test.out: turbine1_test.bc
	$(COMPILER) -lm -o $@ $<

turbine1_test.bc: turbine1_driver.bc $(RTLIB) turbine1.bc
	llvm-link -o $@ $^

turbine1_driver.ll: turbine1_driver.c
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<

# Compile to IR and run report_exceptions pass.
turbine1.ll: turbine1_flat.c
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<
	opt -S $(LLVM_FLAGS) -o $@ $@

%.bc: %.ll
	opt -o $@ $<

.PHONY: clean
clean:
	rm -rf *.o *.ll *.out *.bc opt_*.c unopt_*.c
