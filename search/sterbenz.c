#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include <fenv.h>

/*
 * Sterbenz' average function.
 *
 * Adapted from Barr 2013.
 */
double average(double x, double y) {
  int samesign;
  if ( x >= 0 ) {
    if (y >=0)
      samesign = 1;
    else
      samesign = 0;
  } else {
    if (y >= 0)
      samesign = 0;
    else
      samesign = 1;
  }
  if ( samesign ) {
    if ( y >= x)
      return x + (y-x)/2.0;
    else
      return y + (x-y)/2.0;
  } else
    return (x+y)/2.0;
}
/*
int main(int argc, char** argv) {
  double x = atof(argv[1]);
  double y = atof(argv[2]);

  printf("x=%.10e\n", x);
  printf("y=%.10e\n", y);

  double result = average(x, y);
  printf("avg=%.10e\n", result);
}
*/
