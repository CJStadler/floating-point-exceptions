#include <math.h>
#define TRUE 1
#define FALSE 0
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923078

double ex6_ic(double year){
    double t = (year - 2000.) / 100.;
    double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
    double eta = t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
    double pie = 174.876384 * PI / 180. - t * (869.8089 * S2R - .03536 * S2R * t);
    return t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
}

