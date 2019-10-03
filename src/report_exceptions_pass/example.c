#include <stdio.h>
#include <stdlib.h>
#include <float.h>

#include "exceptions.h"

double over(double x) {
  x *= 2;
  x *= 2;
  return x;
}

double under(double x) {
  return x * x;
}

double invalid(double x) {
  return x / x;
}

double div_by_zero(double x) {
  double y = 10;
  return y / x;
}

int main(int argc, char *argv[]) {
  double x;
  if (argc > 1) {
    x = atof(argv[1]);
  } else {
    x = DBL_MAX;
  }
  printf("x=%f\n", x);
  printf("%f\n", over(x));
  double y = DBL_MIN;
  printf("%f\n", under(y));
  double z = 0;
  printf("%f\n", div_by_zero(z));
  printf("%f\n", invalid(z));
  printf("%f\n", over(x));
  printf("overflows=%i\n", overflows);
  return 0;
}
