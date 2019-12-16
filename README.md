# Floating Point Exceptions

## Dependencies

- LLVM/clang (tested with 8.0.1)
- Python 3 (tested with 3.5.3)
- Z3 (tested with 4.8.6)

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
