#include <float.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  float x = 100;
  float y = 0;
  float result = x / y;
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
