# Exception triggering inputs finder

This project finds inputs that are likely to trigger floating point exceptions
in numerical C programs. For each instruction in the program we build
constraints over the program inputs which when satisfied should trigger a
floating point exception.  The constraints are over the Reals, so there is no
guarantee that an exception will actually be triggered in floating point
execution.

For example, given the following program
```c
double foo(double a, double b) {
  return (a + b);
}
```

We generate a constraint `|a + b| > DBL_MAX` to find inputs that should trigger
an oveflow, and a constraint `|a + b| < DBL_MIN` to find inputs that should
trigger an underflow. Each constraint is then solved and satisfying assignments
are reported.

Programs are input as LLVM IR and parsed into an AST. For each instruction in
the AST a constraint is built and solved using Z3.

## Setup

Tested with python 3.5.3.

Install requirements from `requirements.txt`:
```sh
pip install -r requirements.txt
```

## Usage

Compile a program to LLVM IR:
```sh
$ clang -S -emit-llvm -O1 -o examples/foo.ll examples/foo.c
```
This is the "unoptimized" version, but we still use `O1` so that variables are
not put on the stack. The IR should contain only a sequence of floating point
operations.

Compile the same program with fast math:
```sh
$ clang -S -emit-llvm -O1 -ffast-math -o examples/foo_opt.ll examples/foo.c
```

Generate inputs from both versions:
```sh
$ python3 find_inputs.py examples/foo.ll examples/foo_opt.ll inputs.txt
Made 2 constraints from examples/foo.ll
Made 2 constraints from examples/foo_opt.ll
4 constraints are unique
Solving
....
4 constraints are satisfiable
2 inputs are unique
Saved input solutions to inputs.txt
```

## Limitations

- Programs must only contain a single function.
- All values must be doubles.
- There must be no function calls.
- Loops must be fully unrolled (use `opt -loop-unroll -unroll-count=X`) before
  passing the LLVM IR to this program.

## Development notes

- Type annotations are used and can be checked with mypy.
