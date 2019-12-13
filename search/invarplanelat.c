#include <math.h>

#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

double ex6(double jd){
    double t0 = 2433282.5;
    double theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
    /* Semimajor axis is 488.49 arcseconds at one AU: */
    //double semimajor = 488.49 * (PI / 180.) / 3600.;
    double longitude = (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
    double gamma = 158.996 * (PI / 180.);
    
    /* Calculate latitude on invariable plane: */
    return asin( sin( longitude) * sin( gamma));
}