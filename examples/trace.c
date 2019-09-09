#include <float.h>
#include <stdio.h>
#include <stdlib.h>

double foo(double x) {
  double y = x;
  puts("op1");
  y = y * 2;
  puts("op2");
  y = y * 2;
  return y;
}

int main(void) {
  double x = DBL_MAX;
  double result = foo(x);
  printf("%f\n", result);

  return EXIT_SUCCESS;
}
