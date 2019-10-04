#define _GNU_SOURCE

#include <stdio.h>
#include <float.h>
#include <fenv.h>

#include "../exception_counters.h"

/* Runtime library */

int overflows = 0;
int underflows = 0;
int divbyzeros = 0;
int invalids = 0;

void _printException(char* type) {
  // fprintf(stderr, " %s", type);
}

void check_for_exception(int lineno) {
  // fprintf(stderr, "Checking for exceptions on line %i:", lineno);
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    overflows++;
    _printException("Overflow");
  }

  if (raised & FE_UNDERFLOW) {
    underflows++;
    _printException("Underflow");
  }

  if (raised & FE_DIVBYZERO) {
    divbyzeros++;
    _printException("DivByZero");
  }

  if (raised & FE_INVALID) {
    invalids++;
    _printException("Invalid");
  }

  // fprintf(stderr, "\n");
  feclearexcept(FE_ALL_EXCEPT);
}

