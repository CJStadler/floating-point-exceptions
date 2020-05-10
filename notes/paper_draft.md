# Notes on May 5th draft of paper

Overall this looks good and I didn't find anything that seemed incorrect. The
turbine example could be fleshed out a bit: why does this input trigger an
exception in only P'? I think the main weakness of the paper is just that the
work is preliminary and so we don't have a strong finding or clear application
of the tool. I don't see a way around that at this point though. Here are my
answers to your questions:

1. (page 4) The solver only looks for "invalid" exceptions caused by 0/0 (which
   I believe is all that Barr et al. looks for). Since the solving is over RA it
is not clear to me how you would solve for ∞ - ∞.

2. (page 6) Yes, I implemented the check_for_exception function (in
   report_exceptions_pass/rtlib.cpp), as well as the LLVM pass that inserts a
call to this function after every floating point operation.

3. (page 6) You are right, the global variable used to record the exception
   trace is a list (actually a C++ vector). check_for_exception appends each
exception that it finds to this.

4. (page 6) Given an input candidate, the search program reports the FIRST input
   in the neighborhood for which the behavior of the two programs differs.

5. (page 7) There are some differences between P and P' for carbongas and
   jetengine, but no constant folding. In carbongas the only difference is
rewriting `(a * (n / v)) * (n / v)` as `a * ((n / v) * (n / v))`. It's harder to
understand what the compiler is doing for jetengine, but again there is no
constant folding at least. I've attached both versions of both programs in case
you'd like to take a look.

6. (page 7) Descriptions of each column
  - "Formulae (P, P')": These are the counts of formulae we generated, where
    each formulae represents a particular exception type at a particular
instruction. For each division operation we generate 4 formulae: one each for
overflow, underflow, invalid, and divide by zero. The counts generated from P
and P' are given in parenthesis, and the first number is the count of the union.
  - "Satisfiable": These are the counts of formulae for which Z3 found a
    satisfying assignment.
  - "Unique inputs": Z3 may have reported the same satisfying assignment for
    multiple formulae. These are the counts of satisfying assignments after
removing such duplicates.
  - "Diff producing": These are the counts of satisfying assignments which, when
    given to P and P' as inputs, produced different exception traces (using the
definition given in the paper for "different").

As for the interpretation, here are a few rough ideas: for turbine1, turbine3,
and odometer for about 1/3 of the candidate inputs we were able to find nearby
inputs that produced different behavior. This is perhaps surprising given that
each candidate input was produced only by looking at P or P', but not both. For
jetengine and carbongas we were not able to find any "diff producing" inputs.
There is a correlation between the amount of optimization (rougly measured in
terms of instruction counts) and the number of "diff producing" inputs we found.
If a program has been altered in any significant way by "fast math"
optimizations then our technique is likely to find differences in exception
behavior in the optimized program.

What is the practical application of this tool? Although it is not sound, if the
tool is unable to find any "diff producing" inputs this should give the
developer some confidence that applying "fast math" optimizations will not
produce unexpected differences in behavior. But, as we have seen, when the
optimizations significantly rewrite the program then it is very likely that
there will be "diff producing" inputs.


