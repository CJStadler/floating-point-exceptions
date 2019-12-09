# Exception triggering inputs finder

## Setup

Tested with python 3.5.3.

Install requirements from `requirements.txt`:
```sh
pip install -r requirements.txt
```

## Usage

Compile a program to LLVM IR:
```sh
$ clang -S -emit-llvm -O1 -o examples/turbine1.ll examples/turbine1.c
```
This is the "unoptimized" version, but we still use `O1` so that variables are
not put on the stack. The IR should contain only a sequence of floating point
operations.

Compile the same program with fast math:
```sh
$ clang -S -emit-llvm -O1 -ffast-math -o examples/turbine1_opt.ll examples/turbine1.c
```

Generate inputs from both versions:
```sh
$ python3 compile.py examples/turbine1.ll examples/turbine1_opt.ll inputs.txt
Made 32 constraints from examples/turbine1.ll
Made 26 constraints from examples/turbine1_opt.ll
48 constraints are unique
Solving
................................................
44 constraints are satisfiable
Saved input solutions to inputs.txt
```

## Limitations

- Programs must only contain a single function.
- All values must be doubles.
- There must be no function calls.
