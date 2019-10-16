#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double ex6(double v, double w, double r) {
  return (((3.0 + (2.0 / (r * r))) - (((0.125 * (3.0 - (2.0 * v))) * (((w * w) * r) * r)) / (1.0 - v))) - 4.5);
}

