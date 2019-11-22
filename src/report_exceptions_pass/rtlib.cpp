#include <stdio.h>
#include <float.h>
#include <fenv.h>

#include "../fp_exception.hpp"

/* Runtime library */

ExceptionTrace ex_trace;

void report_exception(ExceptionType type, int lineno) {
  FPException ex;
  ex.type = type;
  ex.lineno = lineno;

  ex_trace.push_back(ex);

  switch (type) {
    case overflow:
      fprintf(stderr, " %s", "Overflow");
      break;
    case underflow:
      fprintf(stderr, " %s", "Underflow");
      break;
    case div_by_zero:
      fprintf(stderr, " %s", "DivByZero");
      break;
    case invalid:
      fprintf(stderr, " %s", "Invalid");
      break;
  }
}

void check_for_exception(int lineno) {
  fprintf(stderr, "Checking for exceptions on line %i:", lineno);
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    report_exception(overflow, lineno);
  }

  if (raised & FE_UNDERFLOW) {
    report_exception(underflow, lineno);
  }

  if (raised & FE_DIVBYZERO) {
    report_exception(div_by_zero, lineno);
  }

  if (raised & FE_INVALID) {
    report_exception(invalid, lineno);
  }

  fprintf(stderr, "\n");
  feclearexcept(FE_ALL_EXCEPT);
}

