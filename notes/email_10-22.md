Hi Thomas,

I took the "turbine1" program (from Yijia's project) and wrote an SMT program by
hand to find inputs that trigger exceptions. Using this I was able to find one
input which triggered an exception in P' which did not occur in P, and the two
programs also had different results on this input.

First I "flattened" the program into a linear sequence of expressions
(turbine1_flat.c in the attachment), as this makes writing the formula easier.
The Ariadne paper does this as well: "For simplicity of presentation, we assume
that nested arithmetic expressions have been flattened" (3).

Then for each expression I wrote the checks described by the Ariadne paper as
SMT formulae (turbine1.smt2). For example, for every multiplication there is one
formula asserting that the result must be greater than DBL_MAX, and one that it
must be less than DBL_MIN. In the paper they add the checks to the C source code
and then extract the formulae using Klee, but since I was doing this by hand it
was easier to skip directly to SMT. In the paper they say "We assume that the
program terminates after throwing a floating-point exception" (3), but I dropped
this assumption because we are interested in exception traces, not just whether
there is any exception. For example, we would like to find an input where P and
P' both overflow, but P' also has an additional underflow later in the program.

Running Z3 on the turbine1.smt2 file gave inputs which satisfied each formula
(except for 2 that were unsat) and so should produce exceptions. I then ran P
and P' on each set of inputs (with reporting exceptions enabled). Here are the results:

Total formulae: 31
unsat: 2
sat: 29
Inputs not representable as a double: 7
Total tested inputs: 22
Exception produced only by P: 1
Exception produced only by P': 1
Exception produced by neither: 8
Exception produced by both: 12

In some cases I did a small amount of manual "searching" around the given input
by rounding in one direction or another. If one of these produced an exception I
counted it.

The most interesting result was with the inputs
v = -0.25
w = 0.125
r = -1.0726246343e+155
These produced an overflow on line 12 only in P'. This also changed the result from
-6.2919259709e+307 in P, to -inf in P'. This suggests to me that if we construct
the formulae only from P we may still be able to find differences from P'.

You should be able to reproduce this with the following:

$ clang -O1 -ffast-math turbine1_driver.c turbine1_flat.c 
$ ./a.out -0.25 0.125 -1.0726246343e+155
ex6(-2.5000000000e-01, 1.2500000000e-01, -1.0726246343e+155) = -inf
$ clang turbine1_driver.c turbine1_flat.c 
$ ./a.out -0.25 0.125 -1.0726246343e+155
ex6(-2.5000000000e-01, 1.2500000000e-01, -1.0726246343e+155) = -6.2919259709e+307

I think the next step should be to automate the above process:
1. Write an LLVM pass which instruments source code with exception checks.
2. Use Klee to generate SMT formulae from the instrumented code.
3. Test each input against P and P', searching if necessary.

Let me know what you think.

Best,
Chris
