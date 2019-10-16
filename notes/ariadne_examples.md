## Sterbenz average

- The `FE_UNDERFLOW` flag is only set if there is a loss of precision in
  addition to the result being less than `DBL_MIN`: https://www.gnu.org/software/libc/manual/html_node/FP-Exceptions.html#FP-Exceptions
- Sterbenz divides by 2, so there is no loss of precision even when the result
  is < `DBL_MIN`.

## GSL

- https://www.gnu.org/software/gsl/doc/html/index.html
- x < 0 gives invalid
- x = 0 gives divbyzero
- "nu = -5.789604e+76 and x = 2.467898e+03" overflow not reproduced
- "nu = -7.458341e-155 and x = 2.197413e+03" underflows.
