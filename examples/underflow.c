#include <float.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  float x = FLT_MIN;
  float result = x / 2;
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
