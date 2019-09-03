#include <float.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  float x = FLT_MAX;
  float result = x * x;
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
