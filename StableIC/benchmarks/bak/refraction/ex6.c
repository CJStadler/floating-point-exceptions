#include <math.h>
#define TRUE 1
#define FALSE 0

#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

double ex6(double observed_alt) {
    double rval, ang = observed_alt;
    
    ang += (7.31 * PI / 180.) / (ang * 180. / PI + 4.4);
    rval = cos( ang) / sin( ang);       /* from Meeus,  _AA_,  p 102 */
    rval -= .06 * sin( (14.7 * rval + 13.) * PI / 180.);
    return( rval * (PI / 180.) / 60.);        /* cvt to radians */
}
