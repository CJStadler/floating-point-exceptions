COMPILER := clang++
PASS_LIB := ../report_exceptions_pass/build/report_exceptions/libReportExceptions.so
LIBS := ../report_exceptions_pass/rtlib.bc ../report_exceptions_pass/fp_exception.bc
CLANG_FLAGS := -Xclang -disable-O0-optnone -ffast-math
LLVM_FLAGS := -load $(PASS_LIB) -report_exceptions

# Strip extensions
NAME := $(basename $(SOURCE))

# This requires two arguments:
#   SOURCE: The name of a C file to test.
#   FUNCTION: The name of the function to test.
#
# The program in SOURCE must define a function
# `double vector_call(std::vector<double)`
# which wraps a call to FUNCTION.
#
# This compiles the program into two objects: one with instcombine and one
# without. In each the function is renamed so that the driver can call them
# both.
search.out: search.bc
	$(COMPILER) -lm -o $@ $<

test.out: test-linked.bc
	$(COMPILER) -lm -o $@ $<

test-linked.bc: test.bc $(LIBS) unopt_$(NAME).bc opt_$(NAME).bc
	llvm-link -o $@ $^

test.ll: test.c
	$(COMPILER) -S -emit-llvm -o $@ $<

search.bc: driver.bc $(LIBS) unopt_$(NAME).bc opt_$(NAME).bc
	llvm-link -o $@ $^

driver.ll: driver.cpp
	$(COMPILER) -S -emit-llvm -o $@ $<

# Compile to IR and run report_exceptions pass.
unopt_$(NAME).ll: unopt_$(SOURCE)
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<
	opt -S $(LLVM_FLAGS) -o $@ $@

# Rename function to p_unopt.
unopt_$(SOURCE): $(SOURCE)
	sed 's/vector_call/p_unopt/g' $< > $@
	sed -i 's/$(FUNCTION)/unopt_fun/g' $@

# Compile to IR and run report_exceptions pass.
opt_$(NAME).ll: opt_$(SOURCE)
	$(COMPILER) -S -emit-llvm -g $(CLANG_FLAGS) -o $@ $<
	opt -S $(LLVM_FLAGS) -instcombine -o $@ $@

# Rename function to p_opt
opt_$(SOURCE): $(SOURCE)
	sed 's/vector_call/p_opt/g' $< > $@
	sed -i 's/$(FUNCTION)/opt_fun/g' $@

%.bc: %.ll
	opt -o $@ $<

.PHONY: clean
clean:
	rm -rf *.o *.ll *.out *.bc opt_* unopt_*

