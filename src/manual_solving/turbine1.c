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
  if (0.0 < abs1 && abs1 < DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  return product;
}

double check_div(double numerator, double denominator) {
  if (denominator == 0.0) {
    if (numerator == 0.0) {
      fprintf(stderr, "Invalid!\n");
    } else {
      fprintf(stderr, "DivByZero!\n");
    }
    exit(1);
  }

  double abs1 = fabs(numerator);
  double abs2 = fabs(denominator);
  if (abs1 > abs2 * DBL_MAX) {
    fprintf(stderr, "Overflow!\n");
    exit(1);
  }
  if (0.0 < abs1 && abs1 < abs2 * DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  return numerator / denominator;
}

double ex6(double v, double w, double r) {
  // Temps used by checks.
  double numerator;
  double denominator;
  double abs1;
  double abs2;

  double t1 = r * r;
  abs1 = fabs(t1);
  if (DBL_MAX < abs1) {
    fprintf(stderr, "Overflow!\n");
    exit(1);
  }
  if (0.0 < abs1 && abs1 < DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  numerator = 2.0;
  denominator = t1;

  if (denominator == 0.0) {
    if (numerator == 0.0) {
      fprintf(stderr, "Invalid!\n");
    } else {
      fprintf(stderr, "DivByZero!\n");
    }
    exit(1);
  }

  abs1 = fabs(numerator);
  abs2 = fabs(denominator);
  if (abs1 > abs2 * DBL_MAX) {
    fprintf(stderr, "Overflow!\n");
    exit(1);
  }
  if (0 < abs1 && abs1 < abs2 * DBL_MIN) {
    fprintf(stderr, "Underflow!\n");
    exit(1);
  }

  double t2 = 2.0 / t1;
  double t3 = 3.0 + t2;
  double t4 = 2.0 * v;
  double t5 = 3.0 - t4;
  double t6 = 0.125 * t5;
  double t7 = w * w;
  double t8 = t7 * r;
  double t9 = t8 * r;
  double t10 = t6 * t9;
  double t11 = 1.0 - v;
  double t12 = t10 / t11;
  double t13 = t3 - t12;
  double t14 = t13 - 4.5;
  return t14;
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
