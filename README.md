# Floating Point Exceptions with Fast Math

## Dependencies

- LLVM/clang (tested with 8.0.1)
- Python 3 (tested with 3.5.3)
- Z3 (tested with 4.8.6)

## Setup

1. Install the above dependencies.

2. Install Python libraries:
```
pip install -r find_inputs/requirements.txt
```

3. Build the LLVM pass that instruments FP instructions with exception checking:
```
make -C report_exceptions_pass/
```

## Run

The main entrypoint is the `find_diff_inputs.py` script. This takes the name of
a C source file to analyze and test.

For example:
```
$ python find_diff_inputs.py examples/turbine1.c 
Compiling examples/turbine1.c -> unopt.ll with ffast-math=False
Compiling examples/turbine1.c -> opt.ll with ffast-math=True
Made 32 constraints from unopt.ll
Made 26 constraints from opt.ll
48 constraints are unique
Solving
................................................
44 constraints are satisfiable
29 inputs are unique
Saved input solutions to inputs.tmp.txt

make: Entering directory '/floating-point-exceptions/search'
sed 's/ex6/target_fun_unopt/g' source.tmp.c > unopt_source.tmp.c
clang -S -emit-llvm -g -Xclang -disable-O0-optnone -ffast-math -o unopt_source.tmp.ll unopt_source.tmp.c
opt -S -load ../report_exceptions_pass/build/report_exceptions/libReportExceptions.so -report_exceptions -o unopt_source.tmp.ll unopt_source.tmp.ll
opt -o unopt_source.tmp.bc unopt_source.tmp.ll
sed 's/ex6/target_fun_opt/g' source.tmp.c > opt_source.tmp.c
clang -S -emit-llvm -g -Xclang -disable-O0-optnone -ffast-math -o opt_source.tmp.ll opt_source.tmp.c
opt -S -load ../report_exceptions_pass/build/report_exceptions/libReportExceptions.so -report_exceptions -instcombine -o opt_source.tmp.ll opt_source.tmp.ll
opt -o opt_source.tmp.bc opt_source.tmp.ll
llvm-link -o search.bc driver.bc bridge_3.bc ../report_exceptions_pass/rtlib.bc ../report_exceptions_pass/fp_exception.bc unopt_source.tmp.bc opt_source.tmp.bc
clang++ -lm -o search.out search.bc
make: Leaving directory '/floating-point-exceptions/search'

Testing inputs from /floating-point-exceptions/inputs.tmp.txt
Input: 7.98974726605473692417e+307 -3.00000000000000088818e+00 9.99999999999999666933e-01
P:  
P': Overflow 
Input: 1.00000000000000000000e+00 0.00000000000000000000e+00 -4.94065645841246544177e-324
P:  Underflow DivByZero Invalid 
P': Underflow DivByZero Underflow Invalid 
Input: 1.50000000000000000000e+00 0.00000000000000000000e+00 -4.94065645841246544177e-324
P:  Underflow DivByZero 
P': Underflow DivByZero Underflow 
Input: -1.25000000000000000000e-01 -5.00000000000000000000e-01 -1.48219693752373963253e-323
P:  Underflow DivByZero Underflow Underflow 
P': Underflow DivByZero Underflow 
Input: 1.59242021634862570474e+308 1.25000000000000000000e-01 -1.70000000000000000000e+01
P:  Overflow 
P': 
Input: 0.00000000000000000000e+00 0.00000000000000000000e+00 -4.94065645841246544177e-324
P:  Underflow DivByZero 
P': Underflow DivByZero Underflow 
Input: 8.98846567431157854073e+307 0.00000000000000000000e+00 -4.94065645841246544177e-324
P:  Underflow DivByZero 
P': Underflow DivByZero Underflow 
Input: 1.25000000000000000000e-01 5.00000000000000000000e-01 -1.48219693752373963253e-323
P:  Underflow DivByZero Underflow Underflow 
P': Underflow DivByZero Underflow 
Input: -1.25000000000000000000e-01 1.25000000000000000000e-01 1.07262463439540764888e+155
P:  Overflow 
P': Overflow Overflow 
Input: 5.00000000000000000000e-01 -5.00000000000000000000e-01 -1.48219693752373963253e-323
P:  Underflow DivByZero Underflow Underflow 
P': Underflow DivByZero Underflow 
Input: -8.98846567431157854073e+307 0.00000000000000000000e+00 -4.94065645841246544177e-324
P:  Underflow DivByZero 
P': Underflow DivByZero Underflow 
Input: 1.59242021634862570474e+308 -1.70000000000000000000e+01 1.25000000000000000000e-01
P:  Overflow 
P': 
Input: -1.79769313486231570815e+308 0.00000000000000000000e+00 0.00000000000000000000e+00
P:  DivByZero Overflow Invalid 
P': DivByZero 
Input: -2.50000000000000000000e-01 -1.25000000000000000000e-01 1.34078079299425970996e+154
P:  Overflow 
P': Overflow Overflow 
Inputs:          29
Exception in P:  25
Exception in P': 24
Diff producing:  14
    Overflow   Underflow  DivByZero  Invalid
P   8          34         51         55       
P'  8          36         53         56
```

If the program has loops they must be unrolled by passing `--unroll-count N`
where `N` is number of iterations.
