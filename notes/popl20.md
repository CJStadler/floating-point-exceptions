# popl20

- How to reduce instability without decreasing efficiency.
- Define equivalency in terms of numeric stability.
- In example (1) clang -ffast-math does not rewrite (gcc does)?
- Sensitivity difference: rounding error difference introduced by
  optimization.
- Stability equivalence: "for every input, the two programs show similar
  rounding-error behavior."
- If stability is corrupted than disable optimization for "worst"
  expressions until stability is preserved.
- Optimization may improve accuracy (relative to real arithmetic).
- Improved accuracy of intermediate result may not lead to better accuracy
  in final.
- "stochastic search": does this mean actual execution?
- Requires specifying input ranges.

- "Step 1 is symbolic: it runs the new pass on P, resulting in code that
  computes local, expression-level error sensitivity differences introduced by
  each optimization rule." How? (p8)
- I don't understand "Expression-Level Sensitivity Analysis" (p11)
- How can rounding error be input independent?

- "Perturbation factors"?
- "Computational process"?
- "numerically stable"?

- Boost interval library
- Why implemented both interval and stochastic?

## Special floating-point data
- Algorithm:
  - Check P and P' for exceptions.
  - If no exceptions, conduct numeric stability.
  - Else, check if exceptions violate stability (the values are
    different?).
- "−NaN compared with anything returns true under -ffast-math compilation
with gcc, false otherwise"
- Ariadne doesn't accept LLVM IR, so we need to apply the optimizations to the
  source code to generate P'.
