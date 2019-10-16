#include <math.h>

/*
 * Optimizations:
 * 1. (.125 * (3.0 - (2.0 * v))) => (0.375 - (0.25 * v))
 * 2. Reuse (r * r) in (((w * w) * r) * r)
 * 3. (((3.0 + (exp1)) - (exp2)) - 4.5) => ((-1.5 + (exp1)) - (exp2))
 */
double ex6(double v, double w, double r) {
  double t1 = r * r;
  double t2 = 2.0 / t1;
  double t4 = 0.25 * v;
  double t6 = 0.375 - t4;
  double t7 = w * w;
  double t9 = t7 * t1;
  double t10 = t6 * t9;
  double t11 = 1.0 - v;
  double t12 = t10 / t11;
  double t13 = t2 - 1.5;
  double t14 = t13 - t12;
  return t14;
}

