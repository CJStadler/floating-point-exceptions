/* triton.cpp: low-precision ephems for Triton
 
 Copyright (C) 2010, Project Pluto
 
 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 02110-1301, USA.    */

#include <math.h>
#include <chrono>
#include <iostream>

#include "theta.h"

// #include "lunar.h"
// #include "afuncs.h"

#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923


#define CVT (PI / 180.)
#define ARCSECONDS_TO_RADIANS (CVT / 3600.)

/* obliquity formula comes from p 135, Meeus,  Astro Algor */
/* input is time in julian centuries from 2000. */
/* rval is mean obliq. (epsilon sub 0) in radians */
/* Valid range is the years -8000 to +12000 (t = -100 to 100) */

double mean_obliquity( const double t_cen);
double asine( const double arg);

/* For the following,  see p 373 of the _Explanatory Supplement_ */
/* Note that 'rocks.cpp' also has code for computing the position of Triton.
 The following is,  therefore,  essentially obsolete.   */

void polar3_to_cartesian( double *vect, const double lon, const double lat);


void pre_spin_matrix( double *v1, double *v2, const double angle);

void spin_matrix( double *v1, double *v2, const double angle);

void set_identity_matrix( double *matrix);

double computePie_ic(double year){
    const double t = (year - 2000.) / 100.;
    const double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
    const double pie = 174.876384 * PI / 180. -
    t * (869.8089 * S2R - .03536 * S2R * t);
    return pie;
}

double computeP_ic(double year){
    const double t = (year - 2000.) / 100.;
    const double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
    return t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
}

double computeEta_ic(double year){
    const double t = (year - 2000.) / 100.;
    const double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
    return t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
}

static int setup_ecliptic_precession_from_j2000_ic( double  *matrix, const double year)
{
    //   const double t = (year - 2000.) / 100.;
    //   const double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
    //   const double eta = t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
    //   const double pie = 174.876384 * PI / 180. -
    //           t * (869.8089 * S2R - .03536 * S2R * t);
    //   const double p = t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
    
    set_identity_matrix( matrix);
#ifdef UNNECESSARY_MATH
    spin_matrix( matrix, matrix + 3, -computePie_ic(year));
#else       /* can get the same result without as much math: */
    matrix[0] = matrix[4] = cos(computePie_ic(year));
    matrix[1] = sin(computePie_ic(year));
    matrix[3] = -matrix[1];
#endif
    spin_matrix( matrix + 3, matrix + 6, -computeEta_ic(year));
    spin_matrix( matrix + 3, matrix, -computeP_ic(year));
    spin_matrix( matrix, matrix + 3, computePie_ic(year));
    return( 0);
}

int setup_precession_ic(double *matrix, const double year_from, const double year_to)
{
    const double obliquity1 = mean_obliquity( (year_from - 2000.) / 100.);
    const double obliquity2 = mean_obliquity( (year_to - 2000.) / 100.);
    
    setup_ecliptic_precession_from_j2000_ic( matrix, year_to);
    pre_spin_matrix( matrix + 1, matrix + 2, obliquity1);
    spin_matrix( matrix + 3, matrix + 6, obliquity2);
    return( 0);
}

int precess_vector( const double  *matrix,
                   const double  *v1,
                   double  *v2);

int deprecess_vector( const double  *matrix,
                     const double  *v1,
                     double  *v2);

int precess_ra_dec( const double *matrix,
                   double  *p_out,
                   const double *p_in, int backward);

double computeLongitude_ic(double jd){
    const double t0 = 2433282.5;
    const double theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
    /* Semimajor axis is 488.49 arcseconds at one AU: */
    const double semimajor = 488.49 * (PI / 180.) / 3600.;
    const double longitude =  //calLongitude(jd);
    (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
    const double gamma = 158.996 * (PI / 180.);
    
    /* Calculate longitude and latitude on invariable plane: */
    return theta + atan2( sin( longitude) * cos( gamma),
                         cos( longitude));
}

double computeLatitude_ic(double jd){
    const double t0 = 2433282.5;
    //const double theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
    /* Semimajor axis is 488.49 arcseconds at one AU: */
    const double semimajor = 488.49 * (PI / 180.) / 3600.;
    const double longitude = //calLongitude(jd);
    (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
    const double gamma = 158.996 * (PI / 180.);
    
    /* Calculate longitude and latitude on invariable plane: */
    
    return asin( sin( longitude) * sin( gamma));
}

void calc_triton_loc_ic( const double jd, double *vect)
{
    const double t_cent = (jd - J2000) / 36525.;
    const double n = (359.28 + 54.308 * t_cent) * (PI / 180.);
    //   const double t0 = 2433282.5;
    //   const double theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
    //            /* Semimajor axis is 488.49 arcseconds at one AU: */
    const double semimajor = 488.49 * (PI / 180.) / 3600.;
    //   const double longitude =
    //               (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
    //   const double gamma = 158.996 * (PI / 180.);
    
    /* Calculate longitude and latitude on invariable plane: */
    const double lon_on_ip = computeLongitude_ic(jd);
    const double lat_on_ip = computeLatitude_ic(jd);
    /* Vectors defining invariable plane,  expressed in B1950: */
    double x_axis[3], y_axis[3], z_axis[3];
    /* Vector defining Triton position in invariable plane space: */
    double triton[3];
    /* RA/dec of the pole: */
    double ra_dec_p[2];
    double matrix[9];
    double vect_1950[3];
    int i;
    
    polar3_to_cartesian( triton, lon_on_ip, lat_on_ip);
    
    ra_dec_p[0] = (298.72 * PI / 180.) + (2.58 * PI / 180.) * sin( n)
    - (0.04 * PI / 180.) * sin( n + n);
    ra_dec_p[1] = (42.63 * PI / 180.) - (1.90 * PI / 180.) * cos( n)
    + (0.01 * PI / 180.) * cos( n + n);
    setup_precession_ic( matrix, 2001, 2002);
    precess_ra_dec( matrix, ra_dec_p, ra_dec_p, 1);
    polar3_to_cartesian( x_axis, ra_dec_p[0] + PI / 2., 0.);
    polar3_to_cartesian( y_axis, ra_dec_p[0] + PI, PI / 2. - ra_dec_p[1]);
    polar3_to_cartesian( z_axis, ra_dec_p[0], ra_dec_p[1]);
    
    for( i = 0; i < 3; i++)
        vect_1950[i] = semimajor * (x_axis[i] * triton[0] +
                                    y_axis[i] * triton[1] + z_axis[i] * triton[2]);
    precess_vector( matrix, vect_1950, vect);
}


