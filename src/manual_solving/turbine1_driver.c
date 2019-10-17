#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double ex6(double, double, double);

int main(int argc, char** argv) {
  if (argc < 4) {
    puts("3 inputs required");
    exit(1);
  }

  double v = atof(argv[1]);
  double w = atof(argv[2]);
  double r = atof(argv[3]);

  double res = ex6(v, w, r);

  printf("ex6(%.10e, %.10e, %.10e) = %.10e\n", v, w, r, res);

  return 0;
}
