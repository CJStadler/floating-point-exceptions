#include <math.h>
#define TRUE 1
#define FALSE 0

double ex6(double v, double w, double r) {
  double t1 = r * r;
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

