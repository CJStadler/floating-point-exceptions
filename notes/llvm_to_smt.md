- Assume single function and no control-flow.
- Assume all vars are float.

## LLVM

- LLVM IR is SSA
- https://llvm.org/doxygen/Parser_8cpp_source.html

## Z3/SMT

- https://github.com/srg-imperial/klee-float/blob/2c533de29b5a3c395b4a0d10f9eaf32a43da1411/lib/Solver/Z3Solver.cpp

```
Z3_solver theSolver = Z3_mk_solver(builder->ctx)
Z3_solver_to_string(builder->ctx, theSolver)
Z3_solver_assert(builder->ctx, theSolver, sideConstraint)
```

- `Z3_solver_assert`

- https://github.com/srg-imperial/klee-float/blob/2c533de29b5a3c395b4a0d10f9eaf32a43da1411/lib/Solver/Z3Builder.cpp

```
Z3ASTHandle Z3Builder::getTrue() { return Z3ASTHandle(Z3_mk_true(ctx), ctx); }
```

## Python?

- Could use http://llvmlite.pydata.org to parse IR, then use Z3's python API to
  build smt.
- llvmlite doesn't expose operand info? `op.__str__()`

## Results

- Checked a few of the solutions and they matched the solutions to my manually
  written formula. Including the inputs which produced a difference between the
  unopt and opt.
