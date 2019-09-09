#include <float.h>
#include <stdio.h>
#include <stdlib.h>

double sqr(double x) {
  return x * x;
}

int main(void) {
  float result = 3;
  float x = FLT_MAX;
  result = sqr(x);
  printf("%.10e\n", result);

  float y = FLT_MIN;
  result = sqr(y);
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
