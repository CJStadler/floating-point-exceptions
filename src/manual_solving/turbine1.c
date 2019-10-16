#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

// We can't actually call this because then it would only need to be reached one
// for coverage. Can it be a macro?
double check_mult(double a, double b) {
  double product = a * b;
  double abs1 = fabs(product);
  if (DBL_MAX < abs1) {
    fprintf(stderr, "Overflow!\n");
    exit(1);
  }
  if (0 < abs1 && abs1 < DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  return product;
}

double ex6(double v, double w, double r) {
  double t1 = r * r;
  double abs1 = fabs(t1);
  if (DBL_MAX < abs1) {
    fprintf(stderr, "Overflow!\n");
    exit(1);
  }
  if (0 < abs1 && abs1 < DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  return (((3.0 + (2.0 / (t1))) - (((0.125 * (3.0 - (2.0 * v))) * (((w * w) * r) * r)) / (1.0 - v))) - 4.5);
}

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
