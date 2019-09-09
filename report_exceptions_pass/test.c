#include <stdio.h>

int foo(int x) {
  return x + 10;
}

int main() {
  int y = 5;
  y += 10;
  printf("x = %i\n", foo(y));
}
