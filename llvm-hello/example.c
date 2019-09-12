#include <stdio.h>
#include <float.h>

double foo(double x) {
  x *= 2;
  x *= 2;
  return x;
}

int main() {
  double x = DBL_MAX;
  printf("%f\n", foo(x));
  return 0;
}
