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

- "Our symbolic execution is standard; the key challenge
in its realization is how to effectively solve the collected numerical
constraints, many of which are multivariate, nonlinear."???
- During symbolic execution reals are used instead of floating-point
  numbers.
- Focuses on bug detection, not proving correctness.
