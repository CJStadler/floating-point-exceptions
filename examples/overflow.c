#include <stdio.h>
#include <stdlib.h>

int main(void) {
  puts("Doing math");
  double x = 999999999999;
  for (int i = 0; i < 10; i++) {
    x = x * x;
  }
  printf("%.10e\n", x);

  puts("finished");
  return EXIT_SUCCESS;
}
