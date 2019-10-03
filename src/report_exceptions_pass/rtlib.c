#define _GNU_SOURCE

#include <stdio.h>
#include <float.h>
#include <fenv.h>

#include "../exception_counters.h"

/* Runtime library */

/* Initialize exception counters */
int overflows = 0;

void _printException(char* type) {
  fprintf(stderr, " %s", type);
}

void check_for_exception(int lineno) {
  fprintf(stderr, "Checking for exceptions on line %i:", lineno);
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    overflows += 1;
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

  fprintf(stderr, "\n");
  feclearexcept(FE_ALL_EXCEPT);
}

