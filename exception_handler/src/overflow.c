#include <float.h>
#include <stdio.h>
#include <stdlib.h>

double sqr(double x) {
  return x * x;
}

int main(void) {
  float x = FLT_MAX;
  float result = sqr(x);
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
