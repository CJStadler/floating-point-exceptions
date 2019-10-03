COMPILER  := clang
PASS_LIB := ../report_exceptions_pass/build/report_exceptions/libReportExceptions.so
RTLIB := ../report_exceptions_pass/rtlib.bc
CLANG_FLAGS := -Xclang -disable-O0-optnone -ffast-math
LLVM_FLAGS := -load $(PASS_LIB) -report_exceptions

# This requires two arguments:
#   SOURCE: The name of a C file to test.
#   FUNCTION: The name of the function in the file to test.
#
# This compiles the program into two objects: one with instcombine and one
# without. In each the function is renamed so that the driver can call them
# both.
search.out: driver.o rtlib.o unopt_$(SOURCE).o opt_$(SOURCE).o
	$(COMPILER) -o $@ $^

rtlib.o:
	llc --filetype=obj -o $@ $(RTLIB)

driver.o: driver.ll
	llc --filetype=obj -o $@ $<

driver.ll: driver.cpp
	$(COMPILER)++ -S -emit-llvm -o $@ $<

# Compile to object and rename function to p_unopt.
unopt_$(SOURCE).o: unopt_$(SOURCE).bc
	llc --filetype=obj -o $@ $<
	objcopy --redefine-sym $(FUNCTION)=p_unopt $@

# Link the runtime library.
unopt_linked_$(SOURCE).bc: unopt_$(SOURCE).bc
	llvm-link -o $@ $(RTLIB) $^

# Compile to IR and run report_exceptions pass.
unopt_$(SOURCE).ll: $(SOURCE)
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<
	opt -S $(LLVM_FLAGS) -o $@ $@

# Compile to object and rename function to p_opt.
opt_$(SOURCE).o: opt_$(SOURCE).bc
	llc --filetype=obj -o $@ $<
	objcopy --redefine-sym $(FUNCTION)=p_opt $@

# Link the runtime library.
opt_linked_$(SOURCE).bc: opt_$(SOURCE).bc
	llvm-link -o $@ $(RTLIB) $^

# Compile to IR and run report_exceptions pass.
opt_$(SOURCE).ll: $(SOURCE)
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<
	opt -S $(LLVM_FLAGS) -instcombine -o $@ $@

%.bc: %.ll
	opt -o $@ $<

.PHONY: clean
clean:
	rm -rf *.o *.ll *.out *.bc
