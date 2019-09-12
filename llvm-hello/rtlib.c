#include <stdio.h>
#include <float.h>

/* Runtime functions */

void _printException(char* type, int lineno) {
  printf("Detected %s on line %i\n", type, lineno);
}

void logop(double i, int lineno) {
  if (i > DBL_MAX) {
    _printException("Overflow", lineno);
  } else if (i < DBL_MIN) {
    _printException("Underflow", lineno);
  }

}

