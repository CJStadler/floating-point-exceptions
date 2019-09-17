#include <stdio.h>
#include <stdlib.h>
#include <float.h>

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
  double x = atof(argv[1]);
  printf("%f\n", over(x));
  double y = DBL_MIN;
  printf("%f\n", under(y));
  double z = 0;
  printf("%f\n", div_by_zero(z));
  printf("%f\n", invalid(z));
  printf("%f\n", over(x));
  return 0;
}
