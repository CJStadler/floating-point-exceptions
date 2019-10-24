# Translating C to SMT

1. Ariadne's approach: modify KLEE to treat floating point as reals.
  - Take advantage of KLEE's power.
  - May be complicated.
2. Write LLVM pass that changes FPs into ints. Apply klee. Change types in smt2
   program from int to Real.
3. Write LLVM pass that spits out an smt2 file.
  - Probably could only handle straight-line pure-FP programs.
4. Use benchmarks written in FPCore (http://fpbench.org/)?
  - There are compilers to smt2 and C.
  - But how to instrument?
5. Do it by hand.
  - Focus on automatically testing the inputs, and searching around them.
