#include <stdlib.h>
#include <float.h>

// Overflows when x > 0.5
int run(double x) {
  double y = DBL_MAX;
  y /= x;
  return y;
}

