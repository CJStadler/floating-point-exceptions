#include <stdio.h>
#include <float.h>

double foo(double x, double y, double z) {
  return (y / x) + (z / x);
}

int main(void) {
  double x = 2;
  double y = DBL_MAX / 2;
  double z = (DBL_MAX / 2) + (DBL_MAX / 4);
  double a = foo(x, y, z);
  printf("%f\n", a);
}
