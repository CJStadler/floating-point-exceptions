#include <math.h>
#define TRUE 1
#define FALSE 0

double ex8_ic(double v, double w, double r) {
    return (((3.0 - (2.0 / (r * r))) - (((0.125 * (1.0 + (2.0 * v))) * (((w * w) * r) * r)) / (1.0 - v))) - 0.5);
}
