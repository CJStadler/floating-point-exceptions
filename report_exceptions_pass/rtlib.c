#define _GNU_SOURCE

#include <stdio.h>
#include <float.h>
#include <fenv.h>

/* Runtime functions */

void _printException(char* type, int lineno) {
  printf("Detected %s on line %i\n", type, lineno);
}

void check_for_exception(int lineno) {
  puts("Checking for exceptions");
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    _printException("Overflow", lineno);
  }

  if (raised & FE_UNDERFLOW) {
    _printException("Underflow", lineno);
  }

  if (raised & FE_DIVBYZERO) {
    _printException("DivByZero", lineno);
  }

  if (raised & FE_INVALID) {
    _printException("Invalid", lineno);
  }

  feclearexcept(FE_ALL_EXCEPT);
}

