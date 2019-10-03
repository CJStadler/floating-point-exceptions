#include <stdio.h>
#include <stdlib.h>
#include <float.h>

int run(double x) {
  double y = DBL_MAX;
  x *= y;
  x /= y;
  return x;
}
