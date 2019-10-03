#include <float.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  float x = 99999999;
  float result = x + 1;
  printf("%.10e\n", result);

  return EXIT_SUCCESS;
}
