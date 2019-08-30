#include <stdio.h>

double diff ( double x ) {
  // the assignment from (1), but evaluated incrementally from left to right
  double P;
  P = 0.5 / x;
  P *= 0.5;
  P += 2.0 / x;
  printf("P = %.20f\n", P);

  // the assignment from (1)
  double Pp = 0.5 / x * 0.5 + 2.0 / x;
  printf("Pp = %.20f\n", Pp);

  return (P - Pp );
}

int main() {
  double d = diff(1000);
  printf("%.20f\n", d);
}
