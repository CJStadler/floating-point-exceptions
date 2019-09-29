#include <math.h>
#define TRUE 1
#define FALSE 0

double ex5(double t, double w) {
    return t + 0.01*(w + 0.01/2*(-9.80665/2.0 * sin(t)));
}
