#include <stdio.h>
#include <mpfr.h>
#include <math.h>

#include "theta.h"

#include <boost/multiprecision/mpfr.hpp>

using namespace boost::multiprecision;
#define PRECISION 256

void calc_triton_loc( const double jd, double *vect);
void calc_triton_loc_ic( const double jd, double *vect);

namespace {
    
#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923
    
    
#define CVT (PI / 180.)
#define ARCSECONDS_TO_RADIANS (CVT / 3600.)
    
    /* obliquity formula comes from p 135, Meeus,  Astro Algor */
    /* input is time in julian centuries from 2000. */
    /* rval is mean obliq. (epsilon sub 0) in radians */
    /* Valid range is the years -8000 to +12000 (t = -100 to 100) */
    
    mpfr_float mean_obliquity( const mpfr_float t_cen)
    {
        mpfr_float u, u0;
        unsigned i;
        const mpfr_float obliquit_minus_100_cen = 24.232841111 * PI / 180.;
        const mpfr_float obliquit_plus_100_cen =  22.611485556 * PI / 180.;
        static mpfr_float j2000_obliquit = 23. * 3600. + 26. * 60. + 21.448;
        static mpfr_float t0 = 30000., rval;
        static long coeffs[10] = { -468093L, -155L, 199925L, -5138L,
            -24967L, -3905L, 712L, 2787L, 579L, 245L };
        
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
        
        rval = j2000_obliquit;
        t0 = t_cen;
        u = u0 = t_cen / 100.;     /* u is in julian 10000's of years */
        for( i = 0; i < 10; i++, u *= u0)
            rval += u * (mpfr_float)coeffs[i] / 100.;
        
        rval *= ARCSECONDS_TO_RADIANS;
        return( rval);
    }
    
    mpfr_float asine( const mpfr_float arg)
    {
        if( arg >= 1.)
            return( PI / 2);
        if( arg <= -1.)
            return( -PI / 2.);
        return( asin( arg));
    }
    
    
    /* For the following,  see p 373 of the _Explanatory Supplement_ */
    /* Note that 'rocks.cpp' also has code for computing the position of Triton.
     The following is,  therefore,  essentially obsolete.   */
    
    void polar3_to_cartesian( mpfr_float *vect, const mpfr_float lon, const mpfr_float lat)
    {
        mpfr_float clat = cos( lat);
        
        *vect++ = cos( lon) * clat;
        *vect++ = sin( lon) * clat;
        *vect   = sin( lat);
    }
    
    
    void pre_spin_matrix( mpfr_float *v1, mpfr_float *v2, const mpfr_float angle)
    {
        const mpfr_float sin_ang = sin( angle);
        const mpfr_float cos_ang = cos( angle);
        int i;
        
        for( i = 3; i; i--)
        {
            const mpfr_float tval = *v1 * cos_ang - *v2 * sin_ang;
            
            *v2 = *v2 * cos_ang + *v1 * sin_ang;
            *v1 = tval;
            v1 += 3;
            v2 += 3;
        }
    }
    
    void spin_matrix( mpfr_float *v1, mpfr_float *v2, const mpfr_float angle)
    {
        const mpfr_float sin_ang = sin( angle);
        const mpfr_float cos_ang = cos( angle);
        int i;
        
        for( i = 3; i; i--)
        {
            const mpfr_float tval = *v1 * cos_ang - *v2 * sin_ang;
            
            *v2 = *v2 * cos_ang + *v1 * sin_ang;
            *v1++ = tval;
            v2++;
        }
    }
    
    void set_identity_matrix( mpfr_float *matrix)
    {
        int i;
        
        for( i = 0; i < 9; i++)
            matrix[i] = ((i & 3) ? 0. : 1.);
    }
    
    mpfr_float computePie(mpfr_float year){
        const mpfr_float t = (year - 2000.) / 100.;
        const mpfr_float S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
        const mpfr_float pie = 174.876384 * PI / 180. -
        t * (869.8089 * S2R - .03536 * S2R * t);
        return pie;
    }
    
    mpfr_float computeP(mpfr_float year){
        const mpfr_float t = (year - 2000.) / 100.;
        const mpfr_float S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
        return t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
    }
    
    mpfr_float computeEta(mpfr_float year){
        const mpfr_float t = (year - 2000.) / 100.;
        const mpfr_float S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
        return t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
    }
    
    static int setup_ecliptic_precession_from_j2000( mpfr_float  *matrix, const mpfr_float year)
    {
        //   const mpfr_float t = (year - 2000.) / 100.;
        //   const mpfr_float S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
        //   const mpfr_float eta = t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
        //   const mpfr_float pie = 174.876384 * PI / 180. -
        //           t * (869.8089 * S2R - .03536 * S2R * t);
        //   const mpfr_float p = t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
        
        set_identity_matrix( matrix);
#ifdef UNNECESSARY_MATH
        spin_matrix( matrix, matrix + 3, -computePie(year));
#else       /* can get the same result without as much math: */
        matrix[0] = matrix[4] = cos(computePie(year));
        matrix[1] = sin(computePie(year));
        matrix[3] = -matrix[1];
#endif
        spin_matrix( matrix + 3, matrix + 6, -computeEta(year));
        spin_matrix( matrix + 3, matrix, -computeP(year));
        spin_matrix( matrix, matrix + 3, computePie(year));
        return( 0);
    }
    
    int setup_precession(mpfr_float *matrix, const mpfr_float year_from, const mpfr_float year_to)
    {
        const mpfr_float obliquity1 = mean_obliquity( (year_from - 2000.) / 100.);
        const mpfr_float obliquity2 = mean_obliquity( (year_to - 2000.) / 100.);
        
        setup_ecliptic_precession_from_j2000( matrix, year_to);
        pre_spin_matrix( matrix + 1, matrix + 2, obliquity1);
        spin_matrix( matrix + 3, matrix + 6, obliquity2);
        return( 0);
    }
    
    int precess_vector( const mpfr_float  *matrix,
                       const mpfr_float  *v1,
                       mpfr_float  *v2)
    {
        int i = 3;
        
        while( i--)
        {
            *v2++ = matrix[0] * v1[0] + matrix[1] * v1[1] + matrix[2] * v1[2];
            matrix += 3;
        }
        return( 0);
    }
    
    int deprecess_vector( const mpfr_float  *matrix,
                         const mpfr_float  *v1,
                         mpfr_float  *v2)
    {
        int i = 3;
        
        while( i--)
        {
            *v2++ = matrix[0] * v1[0] + matrix[3] * v1[1] + matrix[6] * v1[2];
            matrix++;
        }
        return( 0);
    }
    
    int precess_ra_dec( const mpfr_float *matrix,
                       mpfr_float  *p_out,
                       const mpfr_float *p_in, int backward)
    {
        mpfr_float v1[3], v2[3];
        const mpfr_float old_ra = p_in[0];
        
        v1[0] = cos( p_in[0]) * cos( p_in[1]);
        v1[1] = sin( p_in[0]) * cos( p_in[1]);
        v1[2] =                 sin( p_in[1]);
        if( backward)
            deprecess_vector( matrix, v1, v2);
        else
            precess_vector( matrix, v1, v2);
        if( v2[1] != 0. || v2[0] != 0.)
            p_out[0] = atan2( v2[1], v2[0]);
        else
            p_out[0] = 0.;
        p_out[1] = asine( v2[2]);
        while( p_out[0] - old_ra > PI)
            p_out[0] -= PI * 2.;
        while( p_out[0] - old_ra <-PI)
            p_out[0] += PI * 2.;
        return( 0);
    }
    
    mpfr_float computeLongitude(mpfr_float jd){
        const mpfr_float t_cent = (jd - J2000) / 36525.;
        const mpfr_float t0 = 2433282.5;
        const mpfr_float theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
        /* Semimajor axis is 488.49 arcseconds at one AU: */
        const mpfr_float semimajor = 488.49 * (PI / 180.) / 3600.;
        const mpfr_float longitude =
        (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
        const mpfr_float gamma = 158.996 * (PI / 180.);
        
        /* Calculate longitude and latitude on invariable plane: */
        return theta + atan2( sin( longitude) * cos( gamma),
                             cos( longitude));
    }
    
    mpfr_float computeLatitude(mpfr_float jd){
        const mpfr_float t_cent = (jd - J2000) / 36525.;
        const mpfr_float t0 = 2433282.5;
        const mpfr_float theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
        /* Semimajor axis is 488.49 arcseconds at one AU: */
        const mpfr_float semimajor = 488.49 * (PI / 180.) / 3600.;
        const mpfr_float longitude =
        (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
        const mpfr_float gamma = 158.996 * (PI / 180.);
        
        /* Calculate longitude and latitude on invariable plane: */
        
        return asin( sin( longitude) * sin( gamma));
    }
    
    void calc_triton_loc_hp( const mpfr_float jd, mpfr_float *vect)
    {
        const mpfr_float t_cent = (jd - J2000) / 36525.;
        const mpfr_float n = (359.28 + 54.308 * t_cent) * (PI / 180.);
        //   const mpfr_float t0 = 2433282.5;
        //   const mpfr_float theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
        //            /* Semimajor axis is 488.49 arcseconds at one AU: */
        const mpfr_float semimajor = 488.49 * (PI / 180.) / 3600.;
        //   const mpfr_float longitude =
        //               (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
        //   const mpfr_float gamma = 158.996 * (PI / 180.);
        
        /* Calculate longitude and latitude on invariable plane: */
        const mpfr_float lon_on_ip = computeLongitude(jd);
        const mpfr_float lat_on_ip = computeLatitude(jd);
        /* Vectors defining invariable plane,  expressed in B1950: */
        mpfr_float x_axis[3], y_axis[3], z_axis[3];
        /* Vector defining Triton position in invariable plane space: */
        mpfr_float triton[3];
        /* RA/dec of the pole: */
        mpfr_float ra_dec_p[2];
        mpfr_float matrix[9];
        mpfr_float vect_1950[3];
        int i;
        
        polar3_to_cartesian( triton, lon_on_ip, lat_on_ip);
        
        ra_dec_p[0] = (298.72 * PI / 180.) + (2.58 * PI / 180.) * sin( n)
        - (0.04 * PI / 180.) * sin( n + n);
        ra_dec_p[1] = (42.63 * PI / 180.) - (1.90 * PI / 180.) * cos( n)
        + (0.01 * PI / 180.) * cos( n + n);
        setup_precession( matrix, 2001, 2002);
        precess_ra_dec( matrix, ra_dec_p, ra_dec_p, 1);
        polar3_to_cartesian( x_axis, ra_dec_p[0] + PI / 2., 0.);
        polar3_to_cartesian( y_axis, ra_dec_p[0] + PI, PI / 2. - ra_dec_p[1]);
        polar3_to_cartesian( z_axis, ra_dec_p[0], ra_dec_p[1]);
        
        for( i = 0; i < 3; i++)
            vect_1950[i] = semimajor * (x_axis[i] * triton[0] +
                                        y_axis[i] * triton[1] + z_axis[i] * triton[2]);
        precess_vector( matrix, vect_1950, vect);
    }

}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 100; //-4.5;
    double vend= 100.1;//-0.3;
    
    double v = vbegin;
    
    double sigma_ = 0.3;
    double kappa_ = -0.3;
    double rho_ = 0.1;
    double v0_ = 1.5;
    double theta_ = 0.1;
    
    mpfr_float::default_precision(PRECISION);
    
    mpfr_t rhp, remax, re1max, re2max, re, re1, re2;
    mpfr_init2(rhp, PRECISION);
    mpfr_init2(remax, PRECISION);
    mpfr_init2(re1max, PRECISION);
    mpfr_init2(re2max, PRECISION);
    mpfr_init2(re, PRECISION);
    mpfr_init2(re1, PRECISION);
    mpfr_init2(re2, PRECISION);
    
    mpfr_set_d(remax, 0, MPFR_RNDN);
    
    double dist = (nextafter(v, vend)) - v;
    
    for(int i = 0; i < 500000; i ++){
        v= v + dist * pow(2, 10);
        
        double v1[3];
        double v2[3];
        mpfr_float v3[3];
        calc_triton_loc(v, v1);
        calc_triton_loc_ic(v, v2);
        calc_triton_loc_hp(v, v3);
        
        
        for(int i = 0; i < 3; i ++){
            
            mpfr_t temp;
            mpfr_init2(temp, PRECISION);
            mpfr_set_d(temp, 0, MPFR_RNDN);
            
            mpfr_set(rhp, v3[i].backend().data(), GMP_RNDN);
            
            mpfr_sub_d(re1, rhp, v1[i], MPFR_RNDN);
            mpfr_abs(re1, re1, MPFR_RNDN);
            
            mpfr_sub_d(re2, rhp, v2[i], MPFR_RNDN);
            mpfr_abs(re2, re2, MPFR_RNDN);
            

            mpfr_sub(re, re1, re2, MPFR_RNDN);
            mpfr_abs(re, re, MPFR_RNDN);

            if(mpfr_cmp(re, remax) > 0){
                mpfr_set(remax, re, MPFR_RNDN);
                mpfr_set(re1max, re1, MPFR_RNDN);
                mpfr_set(re2max, re2, MPFR_RNDN);
                
                double tl = mpfr_get_d(rhp, MPFR_RNDD);
                double tu = mpfr_get_d(rhp, MPFR_RNDU);
                ulpd = tu - tl;
                //result1 = r1;
                //result2 = r2;
            }
        }
    }
    printf("ULP %.17f\n", ulpd);
    mpfr_printf("RAT %.128RNf\n", remax);
    mpfr_printf("RAT %.128RNf\n", re1max);
    mpfr_printf("RAT %.128RNf\n", re2max);
    
    mpfr_clear(rhp);
    mpfr_clear(remax);
    mpfr_clear(re1max);
    mpfr_clear(re2max);
    mpfr_clear(re);
    mpfr_clear(re1);
    mpfr_clear(re2);
}
