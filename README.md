# Floating Point Exceptions

## Setup

Install dependencies

Build the LLVM pass that instruments FP instructions with exception checking.

```
make -C report_exceptions_pass/
```

## Run

```
python find_diff_inputs.py examples/turbine1.c
```
