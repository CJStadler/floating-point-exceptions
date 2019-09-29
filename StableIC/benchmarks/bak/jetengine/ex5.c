#include <math.h>
#define TRUE 1
#define FALSE 0

double ex5(double x2, double x1) {
  double t = (((3.0 * (x1 * x1)) + (2.0 * x2)) - x1);
  double t_42_ = (((3.0 * (x1 * x1)) - (2.0 * x2)) - x1);
  double d = ((x1 * x1) + 1.0);
  double s = (t / d);
  double s_42_ = (t_42_ / d);
  return (x1 + (((((((((2.0 * x1) * s) * (s - 3.0)) + ((x1 * x1) * ((4.0 * s) - 6.0))) * d) + ((3.0 * (x1 * x1)) * s)) + ((x1 * x1) * x1)) + x1) + (3.0 * s_42_)));
}
