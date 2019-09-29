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

double matrix[9] = {0};

double mean_obliquity_ic(double t_cen) __attribute__((always_inline))
{
   double u, u0;
   unsigned i;
   double obliquit_minus_100_cen = 24.232841111 * PI / 180.;
   double obliquit_plus_100_cen =  22.611485556 * PI / 180.;
   double j2000_obliquit = 23. * 3600. + 26. * 60. + 21.448;
   double t0 = 30000., rval;
   const double coeffs[10] = { -468093, -155, 199925, -5138,
            -24967, -3905, 712, 2787, 579, 245};

   if( t_cen == 0.)      /* common J2000 case;  don't do any math */
      return( j2000_obliquit * ARCSECONDS_TO_RADIANS);
#ifndef CLIP_OBLIQUITY
   else if( t_cen > 100.)      /* Diverges outside +/- 10 millennia,  */
      return( obliquit_plus_100_cen);
   else if( t_cen < -100.)  /* so we might as well clip to that  */
      return( obliquit_minus_100_cen);
#endif

   if( t0 == t_cen)    /* return previous answer */
      return( rval);

   t0 = t_cen;
   u = u0 = t_cen / 100.;     /* u is in julian 10000's of years */
   double sum = 0;
   for( i = 0; i < 10; i++, u *= u0)
       sum += u * (double)coeffs[i] / 100.;

   rval = (j2000_obliquit + sum) * ARCSECONDS_TO_RADIANS;
   return( rval);
}

/* For the following,  see p 373 of the _Explanatory Supplement_ */
/* Note that 'rocks.cpp' also has code for computing the position of Triton.
The following is,  therefore,  essentially obsolete.   */

void polar3_to_cartesian_ic( double *vect, const double lon, const double lat) __attribute__((always_inline))
{
   double clat = cos( lat);

   *vect++ = cos( lon) * clat;
   *vect++ = sin( lon) * clat;
   *vect   = sin( lat);
}


void set_identity_matrix_ic() __attribute__((always_inline))
{
   int i;

   for( i = 0; i < 9; i++)
      matrix[i] = ((i & 3) ? 0. : 1.);
}

static int setup_ecliptic_precession_from_j2000_ic(double year) __attribute__((always_inline))
{
   double t = (year - 2000.) / 100.;
   double S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
   double eta = t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
   double pie = 174.876384 * PI / 180. -
           t * (869.8089 * S2R - .03536 * S2R * t);
   double p = t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);

   set_identity_matrix_ic();
//#ifdef UNNECESSARY_MATH
//   spin_matrix_ic(matrix, matrix + 3, -pie);
//#else       /* can get the same result without as much math: */
   matrix[0] = matrix[4] = cos(pie);
   matrix[1] = sin(pie);
   matrix[3] = -matrix[1];
//#endif

    double sin_ang = sin( -eta);
    double cos_ang = cos( -eta);

    for(int i = 0; i < 3; i ++){
        int v1 = 3 + i;
        int v2 = 6 + i;
        double tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
        matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
        matrix[v1] = tval;
    }
    
    sin_ang = sin( -p);
    cos_ang = cos( -p);
    
    for(int i = 0; i < 3; i ++){
        int v1 = 3 + i;
        int v2 = i;
        double tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
        matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
        matrix[v1] = tval;
    }

    sin_ang = sin(pie);
    cos_ang = cos(pie);
    
    for(int i = 0; i < 3; i ++){
        int v1 = i;
        int v2 = 3 + i;
        double tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
        matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
        matrix[v1] = tval;
    }
   return( 0);
}

int setup_precession_ic(double year_from, double year_to) __attribute__((always_inline))
{
    double obliquity[2];
    obliquity[0] = mean_obliquity_ic( (year_from - 2000.) / 100.);
    obliquity[1] = mean_obliquity_ic( (year_to - 2000.) / 100.);

    setup_ecliptic_precession_from_j2000_ic(year_to);
    
    double sin_ang = sin( obliquity[0]);
    double cos_ang = cos( obliquity[0]);
    for(int i = 0; i < 3; i ++){
        int v1 = 1 + i * 3;
        int v2 = 2 + i * 3;
        
        double tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
        matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
        matrix[v1] = tval;
    }

    sin_ang = sin( obliquity[1]);
    cos_ang = cos( obliquity[1]);
    for(int i = 0; i < 3; i ++){
        int v1 = 3 + i;
        int v2 = 6 + i;
        
        double tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
        matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
        matrix[v1] = tval;
    }
   return( 0);
}


int precess_vector_ic(
                                       double  *v1,
                                      double  *v2) __attribute__((always_inline))
{
    for(int i = 0; i < 3; i++){
      *v2++ = matrix[0 + 3*i] * v1[0] + matrix[1 + 3 * i] * v1[1] + matrix[2 + 3 *i] * v1[2];
    }
   return( 0);
}

int deprecess_vector_ic(
                                       double  *v1,
                                      double  *v2) __attribute__((always_inline))
{
   int i = 3;

  for(int i = 0; i < 3; i++){
      v2[i] = matrix[0 + i] * v1[0] + matrix[3 + i] * v1[1] + matrix[6 + i] * v1[2];
   }
   return( 0);
}

int precess_ra_dec_ic(
                        double  *p_out,
                        const double *p_in, int backward) __attribute__((always_inline))
{
   double v1[3], v2[3], old_ra[1];
   old_ra[0] = p_in[0];

   v1[0] = cos( p_in[0]) * cos( p_in[1]);
   v1[1] = sin( p_in[0]) * cos( p_in[1]);
   v1[2] =                 sin( p_in[1]);
    if( backward){
      deprecess_vector_ic(  v1, v2);
    }
    else{
      precess_vector_ic( v1, v2);
    }
    if( v2[1] != 0. || v2[0] != 0.){
      p_out[0] = atan2( v2[1], v2[0]);
    }else{
      p_out[0] = 0.;
    }

    if( v2[2] >= 1.){
        p_out[1] = ( PI / 2);
    }else if( v2[2] <= -1.){
        p_out[1] = ( -PI / 2.);
    }else{
       p_out[1] = ( asin( v2[2]));
    }

   while( p_out[0] - old_ra[0] > PI)
      p_out[0] -= PI * 2.;
   while( p_out[0] - old_ra[0] <-PI)
      p_out[0] += PI * 2.;
   return( 0);
}


double triton_ic( const double jd) __attribute__((always_inline))
{
   const double t_cent = (jd - J2000) / 36525.;
   const double n = (359.28 + 54.308 * t_cent) * (PI / 180.);
   const double t0 = 2433282.5;
   const double theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
            /* Semimajor axis is 488.49 arcseconds at one AU: */
     const double semimajor = 488.49 * (PI / 180.) / 3600.;
   const double longitude =
               (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
   const double gamma = 158.996 * (PI / 180.);

         /* Calculate longitude and latitude on invariable plane: */
    const double lon_on_ip = theta + atan2( sin( longitude) * cos( gamma),
                                           cos( longitude));
   const double lat_on_ip = asin( sin( longitude) * sin( gamma));
         /* Vectors defining invariable plane,  expressed in B1950: */
   double x_axis[3], y_axis[3], z_axis[3];
         /* Vector defining Triton position in invariable plane space: */
   double triton[3];
         /* RA/dec of the pole: */
   double ra_dec_p[2];

   double vect_1950[3];
    int i;

    triton[0] = cos(lon_on_ip) * cos(lat_on_ip);
   
    triton[1] = sin(lon_on_ip) * cos(lat_on_ip);

    triton[2] = sin(lat_on_ip);

    ra_dec_p[0] = (298.72 * PI / 180.) + (2.58 * PI / 180.) * sin( n)
                     - (0.04 * PI / 180.) * sin( n + n);
    ra_dec_p[1] = (42.63 * PI / 180.) - (1.90 * PI / 180.) * cos( n)
                     + (0.01 * PI / 180.) * cos( n + n);
  
    setup_precession_ic(2001, 2002);
    
    precess_ra_dec_ic(ra_dec_p, ra_dec_p, 1);
    polar3_to_cartesian_ic( x_axis, ra_dec_p[0] + PI / 2., 0.);
    polar3_to_cartesian_ic( y_axis, ra_dec_p[0] + PI, PI / 2. - ra_dec_p[1]);
    double clat = cos( ra_dec_p[1]);
    z_axis[0] = cos( ra_dec_p[0]) * clat;
    z_axis[1] = sin( ra_dec_p[0]) * clat;
    z_axis[2]  = sin(ra_dec_p[1]);
    
   for( i = 0; i < 3; i++)
      vect_1950[i] = semimajor * (x_axis[i] * triton[0] +
                      y_axis[i] * triton[1] + z_axis[i] * triton[2]);


   return matrix[0] * vect_1950[0] + matrix[3] * vect_1950[1] + matrix[6] * vect_1950[2];
    
}

