#include <stdio.h>
#include <float.h>

int main() {
  double x = DBL_MAX;
  puts("op1");
  x *= 2;
  puts("op2");
  x *= 2;
  printf("%f\n", x);
  return 0;
}
