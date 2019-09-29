#include <math.h>
#include <stdio.h>
#include "theta.h"
#define TRUE 1
#define FALSE 0

#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

double ex5_ic(double t_centuries, double ra, double dec) {
    double m = (3.07496 + .00186 * t_centuries / 2.) * (PI / 180.) / 240.;
    double n = (1.33621 - .00057 * t_centuries / 2.) * (PI / 180.) / 240.;
    //double n = caln(t_centuries);
    double ra_rate  = m + n * sin(ra) * tan(dec);
    return ra - t_centuries * ra_rate * 100.;
    
}

