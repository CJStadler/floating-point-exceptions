#include <math.h>
#include <chrono>
#include <limits>
#include <iostream>
#include <stdlib.h>


#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

/*
 REFRACT.CPP contains functions to convert an observed altitude
 (one affected by refraction) to a true altitude (one that would be
 seen on an airless planet),  or vice versa.  The first case is
 handled using the method of G G Bennett,  'The Calculation of
 Astronomical Refraction in Marine Navigation',  _Journal of the
 Institute for Navigation_, Vol 35, p 255-259 (1982),  as explained
 in Meeus' _Astronomical Algorithms_,  p 102.  The maximum error of
 this is stated to be .9 arcsecond,  for the range 0-90 degrees.
 
 For the inverse problem,  handled in the function reverse_refraction(),
 we first get a "pretty good" answer using the formula of Saemundsson,
 _Sky & Telescope_,  p 70,  July 1986,  again as explained in _AA_.
 The only problem is that this formula is accurate to within about 4".
 One iteration using the refraction( ) function repairs this problem.
 
 All inputs and outputs from these functions are in radians.
 */

double refraction( const double observed_alt) __attribute__((always_inline))
{
    double rval, ang = observed_alt;
    
    ang += (7.31 * PI / 180.) / (ang * 180. / PI + 4.4);
    rval = cos( ang) / sin( ang);       /* from Meeus,  _AA_,  p 102 */
    rval -= .06 * sin( (14.7 * rval + 13.) * PI / 180.);
    return( rval * (PI / 180.) / 60.);        /* cvt to radians */
}

double computeApproxRefract(const double true_alt)__attribute__((always_inline))
{
    double rval;
    rval = true_alt + (10.3 * PI / 180.) / (true_alt * 180. / PI + 5.11);
    rval = cos( rval) / sin( rval);  /* from Meeus,  _AA_,  p 102 */
    rval *= 1.02 * (PI / 180.) / 60.;        /* cvt to radians */
    return rval;
}

double reverse_refraction( const double true_alt)__attribute__((always_inline))
{
    double delta = 1;
    int n_iter = 10;
    const double tolerance = .01 * (PI / 180.) / 3600.;
    double rval = computeApproxRefract(true_alt);
    /* The above gives a good first approximation */
    /* Now improve that answer as follows: */
    while( n_iter-- && (delta > tolerance || delta < -tolerance))
    {
        delta = rval;
        rval = refraction( true_alt + rval);
        delta -= rval;
    }
    return( rval);
}

double  saasta_refraction( const double observed_alt,
                          const double pressure_mb, const double temp_kelvin,
                          const double relative_humidity)__attribute__((always_inline))
{
    double xi;
    const double tan_z0 = cos( observed_alt) / sin( observed_alt);
    const double tan_z0_2 = tan_z0 * tan_z0;
    const double delta = 18.36;
    const double pw0 =
    relative_humidity * exp( delta * log( temp_kelvin / 247.1));
    const double q = (pressure_mb - .156 * pw0) / temp_kelvin;
   
    xi = 16.271 * q * tan_z0 * (1. + .0000394 * q * tan_z0_2) -
    .0000749 * pressure_mb * tan_z0 * (1. + tan_z0_2);
    return xi;
    /* The above refraction is in _arcseconds_... */
    return( xi * (PI / 180.) / 3600.);        /* cvt to radians */
}

#define pressure_mb 1013
#define temp_kelvin 293
#define relative_humidity 0.50

double  reverse_saasta_refraction( const double true_alt)
{
//    double rval;
////    double xi;
////    double observed_alt,tan_z0,tan_z0_2,delta,pw0,q;
////
////    rval = true_alt + (10.3 * PI / 180.) / (true_alt * 180. / PI + 5.11);
////    rval = cos( rval) / sin( rval);  /* from Meeus,  _AA_,  p 102 */
////    rval *= 1.02 * (PI / 180.) / 60.;        /* cvt to radians */
////
////
////    observed_alt = true_alt + rval;
////    tan_z0 = cos( observed_alt) / sin( observed_alt);
////    tan_z0_2 = tan_z0 * tan_z0;
////    delta = 18.36;
////    pw0 =
////    relative_humidity * exp( delta * log( temp_kelvin / 247.1));
////    q = (pressure_mb - .156 * pw0) / temp_kelvin;
////
////    xi = 16.271 * q * tan_z0 * (1. + .0000394 * q * tan_z0_2) -
////    .0000749 * pressure_mb * tan_z0 * (1. + tan_z0_2);
////    /* The above refraction is in _arcseconds_... */
////    rval = ( xi * (PI / 180.) / 3600.);        /* cvt to radians */
//    //rval = computeRval2(xi);
//
//    rval = computeApproxRefract(true_alt);
//    /* The above gives a good first approximation */
//    /* Now improve that answer as follows: */
//    rval = saasta_refraction( true_alt + rval,
//                             pressure_mb, temp_kelvin, relative_humidity);
    double t1 = (3 + 2*true_alt)*5;
    double t2 = (5 + 2*true_alt)*7;
    double t3 = (7 + 2*true_alt)*9;
    return cos(t1 + t2 + t3);
}

