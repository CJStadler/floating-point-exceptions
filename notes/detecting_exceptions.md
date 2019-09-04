# Automatic Detection of Floating-Point Exceptions

- Real input found by SMT is unlikely to be representable as a
  floating-point number, but we can search the neighborhood for a fp number
  that also triggers the exception.
- KLEE + Z3

1. Automatically add checks for fp exceptions to program. This makes
   symbolic execution possible.
2. Symbolically execute transformed program, finding assignments that
   trigger the fp exceptions.
3. Search for fp numbers which also  trigger exception.

- Ignores inexact exceptions because they are unavoidable.
- "Our symbolic execution is standard; the key challenge
in its realization is how to effectively solve the collected numerical
constraints, many of which are multivariate, nonlinear."???
- During symbolic execution reals are used instead of floating-point
  numbers.
- Focuses on bug detection, not proving correctness.

## Soundness

- Paper does not explicitly address soundness.
- Identifies inputs which trigger exceptions in real arithmetic (RA). Can there
  be no exceptions in RA, but exist exceptions if FP?
  - Every FP numer is also an RA number, so there should be no such exceptions?
- "Approximating floating-point arithmetic with real arithmetic can also produce
  false negatives, again due to rounding." (6)
- "Ariadne cannot guarantee that a program is exception-free, for three reasons:
  it 1) approximates floating-point semantics with constraints over the reals,
  which notably ignore rounding (i.e. Inexact); 2) concretizes multivariate into
  univariate constraints; and 3) rewrites loop conditions to bound the number of
  iterations." (6)
