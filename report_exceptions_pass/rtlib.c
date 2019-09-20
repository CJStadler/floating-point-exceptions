#define _GNU_SOURCE

#include <stdio.h>
#include <float.h>
#include <fenv.h>

/* Runtime functions */

void _printException(char* type) {
  fprintf(stderr, "Detected %s\n", type);
}

void check_for_exception(int lineno) {
  fprintf(stderr, "Checking for exceptions on line %i\n", lineno);
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    _printException("Overflow");
  }

  if (raised & FE_UNDERFLOW) {
    _printException("Underflow");
  }

  if (raised & FE_DIVBYZERO) {
    _printException("DivByZero");
  }

  if (raised & FE_INVALID) {
    _printException("Invalid");
  }

  feclearexcept(FE_ALL_EXCEPT);
}

