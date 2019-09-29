#include <math.h>
#include <chrono>
#include <limits>
#include <iostream>
#include <stdlib.h>

double  reverse_saasta_refraction_ic( const double true_alt)__attribute__((always_inline))
{
    double rval;
//    double xi;
//    double observed_alt,tan_z0,tan_z0_2,delta,pw0,q;
//
//    //    double rval;
//    rval = true_alt + (10.3 * PI / 180.) / (true_alt * 180. / PI + 5.11);
//    rval = cos( rval) / sin( rval);  /* from Meeus,  _AA_,  p 102 */
//    rval *= 1.02 * (PI / 180.) / 60.;        /* cvt to radians */
//
//    
//    observed_alt = true_alt + rval;
//    tan_z0 = cos( observed_alt) / sin( observed_alt);
//    tan_z0_2 = tan_z0 * tan_z0;
//    delta = 18.36;
//    pw0 =
//    relative_humidity * exp( delta * log( temp_kelvin / 247.1));
//    q = (pressure_mb - .156 * pw0) / temp_kelvin;
//
//    xi = 16.271 * q * tan_z0 * (1. + .0000394 * q * tan_z0_2) -
//    .0000749 * pressure_mb * tan_z0 * (1. + tan_z0_2);
//    /* The above refraction is in _arcseconds_... */
//    rval = ( xi * (PI / 180.) / 3600.);        /* cvt to radians */
    //rval = computeRval2(xi);
//
//    rval = computeApproxRefract_ic(true_alt);
//    /* The above gives a good first approximation */
//    /* Now improve that answer as follows: */
//    rval = saasta_refraction_ic( true_alt + rval,
//                             pressure_mb, temp_kelvin, relative_humidity);
    
    double t1 = (3 + 2*true_alt)*5;
    double t2 = (5 + 2*true_alt)*7;
    double t3 = (7 + 2*true_alt)*9;
    return cos(t1 + t2 + t3);
}

