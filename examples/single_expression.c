#include <stdio.h>

double foo(double x) {
  double y = 0.5 / x * 0.5 + 2.0 / x;
  return y;
}

int main(void) {
  double x = 1000;

  printf("for x = %f\n", x);
  double y = foo(x);
  printf("0.5 / x * 0.5 + 2.0 / x = %.20f\n", y);

  double yy = 2.25 / x;
  printf("               2.25 / x = %.20f\n", yy);
}
