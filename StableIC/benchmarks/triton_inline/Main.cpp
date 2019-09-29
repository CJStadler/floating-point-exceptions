#include <stdio.h>
#include <mpfr.h>
#include <math.h>

#include <boost/multiprecision/mpfr.hpp>

using namespace boost::multiprecision;
#define PRECISION 256

double triton(const double jd);
double triton_ic( const double jd);

namespace {
    
#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923
    
    
#define CVT (PI / 180.)
#define ARCSECONDS_TO_RADIANS (CVT / 3600.)
    
    /* obliquity formula comes from p 135, Meeus,  Astro Algor */
    /* input is time in julian centuries from 2000. */
    /* rval is mean obliq. (epsilon sub 0) in radians */
    /* Valid range is the years -8000 to +12000 (t = -100 to 100) */
    
    /* obliquity formula comes from p 135, Meeus,  Astro Algor */
    /* input is time in julian centuries from 2000. */
    /* rval is mean obliq. (epsilon sub 0) in radians */
    /* Valid range is the years -8000 to +12000 (t = -100 to 100) */
    
    /* obliquity formula comes from p 135, Meeus,  Astro Algor */
    /* input is time in julian centuries from 2000. */
    /* rval is mean obliq. (epsilon sub 0) in radians */
    /* Valid range is the years -8000 to +12000 (t = -100 to 100) */
    
    mpfr_float matrix[9] = {0};
    
    mpfr_float mean_obliquity(mpfr_float t_cen) __attribute__((always_inline))
    {
        mpfr_float u, u0;
        unsigned i;
        mpfr_float obliquit_minus_100_cen = 24.232841111 * PI / 180.;
        mpfr_float obliquit_plus_100_cen =  22.611485556 * PI / 180.;
        mpfr_float j2000_obliquit = 23. * 3600. + 26. * 60. + 21.448;
        mpfr_float t0 = 30000., rval;
        const mpfr_float coeffs[10] = { -468093, -155, 199925, -5138,
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
        mpfr_float sum = 0;
        for( i = 0; i < 10; i++, u *= u0)
            sum += u * (mpfr_float)coeffs[i] / 100.;
            
            rval = (j2000_obliquit + sum) * ARCSECONDS_TO_RADIANS;
            return( rval);
    }
    
    /* For the following,  see p 373 of the _Explanatory Supplement_ */
    /* Note that 'rocks.cpp' also has code for computing the position of Triton.
     The following is,  therefore,  essentially obsolete.   */
    
    void polar3_to_cartesian( mpfr_float *vect, const mpfr_float lon, const mpfr_float lat) __attribute__((always_inline))
    {
        mpfr_float clat = cos( lat);
        
        *vect++ = cos( lon) * clat;
        *vect++ = sin( lon) * clat;
        *vect   = sin( lat);
    }
    
    
    void set_identity_matrix() __attribute__((always_inline))
    {
        int i;
        
        for( i = 0; i < 9; i++)
            matrix[i] = ((i & 3) ? 0. : 1.);
            }
    
    static int setup_ecliptic_precession_from_j2000(mpfr_float year) __attribute__((always_inline))
    {
        mpfr_float t = (year - 2000.) / 100.;
        mpfr_float S2R = (PI / 180.) / 3600.;   /* converts arcSeconds to Radians */
        mpfr_float eta = t * (47.0029 * S2R + (-.03302 * S2R + 6.e-5 * S2R * t) * t);
        mpfr_float pie = 174.876384 * PI / 180. -
        t * (869.8089 * S2R - .03536 * S2R * t);
        mpfr_float p = t * (5029.0966 * S2R + (1.11113 * S2R - 6.e-5 * S2R * t) * t);
        
        set_identity_matrix();
        //#ifdef UNNECESSARY_MATH
        //   spin_matrix_ic(matrix, matrix + 3, -pie);
        //#else       /* can get the same result without as much math: */
        matrix[0] = matrix[4] = cos(pie);
        matrix[1] = sin(pie);
        matrix[3] = -matrix[1];
        //#endif
        
        mpfr_float sin_ang = sin( -eta);
        mpfr_float cos_ang = cos( -eta);
        
        for(int i = 0; i < 3; i ++){
            int v1 = 3 + i;
            int v2 = 6 + i;
            mpfr_float tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
            matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
            matrix[v1] = tval;
        }
        
        sin_ang = sin( -p);
        cos_ang = cos( -p);
        
        for(int i = 0; i < 3; i ++){
            int v1 = 3 + i;
            int v2 = i;
            mpfr_float tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
            matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
            matrix[v1] = tval;
        }
        
        sin_ang = sin(pie);
        cos_ang = cos(pie);
        
        for(int i = 0; i < 3; i ++){
            int v1 = i;
            int v2 = 3 + i;
            mpfr_float tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
            matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
            matrix[v1] = tval;
        }
        return( 0);
    }
    
    int setup_precession(mpfr_float year_from, mpfr_float year_to) __attribute__((always_inline))
    {
        mpfr_float obliquity[2];
        obliquity[0] = mean_obliquity( (year_from - 2000.) / 100.);
        obliquity[1] = mean_obliquity( (year_to - 2000.) / 100.);
        
        setup_ecliptic_precession_from_j2000(year_to);
        
        mpfr_float sin_ang = sin( obliquity[0]);
        mpfr_float cos_ang = cos( obliquity[0]);
        for(int i = 0; i < 3; i ++){
            int v1 = 1 + i * 3;
            int v2 = 2 + i * 3;
            
            mpfr_float tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
            matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
            matrix[v1] = tval;
        }
        
        sin_ang = sin( obliquity[1]);
        cos_ang = cos( obliquity[1]);
        for(int i = 0; i < 3; i ++){
            int v1 = 3 + i;
            int v2 = 6 + i;
            
            mpfr_float tval = matrix[v1] * cos_ang - matrix[v2] * sin_ang;
            matrix[v2] = matrix[v2] * cos_ang + matrix[v1] * sin_ang;
            matrix[v1] = tval;
        }
        return( 0);
    }
    
    
    int precess_vector(
                       mpfr_float  *v1,
                       mpfr_float  *v2) __attribute__((always_inline))
    {
        for(int i = 0; i < 3; i++){
            *v2++ = matrix[0 + 3*i] * v1[0] + matrix[1 + 3 * i] * v1[1] + matrix[2 + 3 *i] * v1[2];
        }
        return( 0);
    }
    
    int deprecess_vector(
                         mpfr_float  *v1,
                         mpfr_float  *v2) __attribute__((always_inline))
    {
        int i = 3;
        
        for(int i = 0; i < 3; i++){
            v2[i] = matrix[0 + i] * v1[0] + matrix[3 + i] * v1[1] + matrix[6 + i] * v1[2];
        }
        return( 0);
    }
    
    int precess_ra_dec(
                       mpfr_float  *p_out,
                       const mpfr_float *p_in, int backward) __attribute__((always_inline))
    {
        mpfr_float v1[3], v2[3], old_ra[1];
        old_ra[0] = p_in[0];
        
        v1[0] = cos( p_in[0]) * cos( p_in[1]);
        v1[1] = sin( p_in[0]) * cos( p_in[1]);
        v1[2] =                 sin( p_in[1]);
        if( backward){
            deprecess_vector(  v1, v2);
        }
        else{
            precess_vector( v1, v2);
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
    
    
    mpfr_float triton_hp( const double jd) __attribute__((always_inline))
    {
        const mpfr_float t_cent = (jd - J2000) / 36525.;
        const mpfr_float n = (359.28 + 54.308 * t_cent) * (PI / 180.);
        const mpfr_float t0 = 2433282.5;
        const mpfr_float theta = (151.401 + .57806 * (jd - t0) / 365.25) * (PI / 180.);
        /* Semimajor axis is 488.49 arcseconds at one AU: */
        const mpfr_float semimajor = 488.49 * (PI / 180.) / 3600.;
        const mpfr_float longitude =
        (200.913 + 61.2588532 * (jd - t0)) * (PI / 180.);
        const mpfr_float gamma = 158.996 * (PI / 180.);
        
        /* Calculate longitude and latitude on invariable plane: */
        const mpfr_float lon_on_ip = theta + atan2( sin( longitude) * cos( gamma),
                                               cos( longitude));
        const mpfr_float lat_on_ip = asin( sin( longitude) * sin( gamma));
        /* Vectors defining invariable plane,  expressed in B1950: */
        mpfr_float x_axis[3], y_axis[3], z_axis[3];
        /* Vector defining Triton position in invariable plane space: */
        mpfr_float triton[3];
        /* RA/dec of the pole: */
        mpfr_float ra_dec_p[2];
        
        mpfr_float vect_1950[3];
        int i;
        
        triton[0] = cos(lon_on_ip) * cos(lat_on_ip);
        
        triton[1] = sin(lon_on_ip) * cos(lat_on_ip);
        
        triton[2] = sin(lat_on_ip);
        
        ra_dec_p[0] = (298.72 * PI / 180.) + (2.58 * PI / 180.) * sin( n)
        - (0.04 * PI / 180.) * sin( n + n);
        ra_dec_p[1] = (42.63 * PI / 180.) - (1.90 * PI / 180.) * cos( n)
        + (0.01 * PI / 180.) * cos( n + n);
        
        setup_precession(2001, 2002);
        
        precess_ra_dec(ra_dec_p, ra_dec_p, 1);
        polar3_to_cartesian( x_axis, ra_dec_p[0] + PI / 2., 0.);
        polar3_to_cartesian( y_axis, ra_dec_p[0] + PI, PI / 2. - ra_dec_p[1]);
        mpfr_float clat = cos( ra_dec_p[1]);
        z_axis[0] = cos( ra_dec_p[0]) * clat;
        z_axis[1] = sin( ra_dec_p[0]) * clat;
        z_axis[2]  = sin(ra_dec_p[1]);
        
        for( i = 0; i < 3; i++)
            vect_1950[i] = semimajor * (x_axis[i] * triton[0] +
                                        y_axis[i] * triton[1] + z_axis[i] * triton[2]);
            
            
            return matrix[0] * vect_1950[0] + matrix[3] * vect_1950[1] + matrix[6] * vect_1950[2];
        
    }


}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;

    double vbegin = 5; //-4.5;
    double vend= 5.1;//-0.3;
    double v = vbegin;
    
    mpfr_float::default_precision(PRECISION);
    
    mpfr_t rhp, redmax, redmax_re1, redmax_re2, re1max, re2max, re, re1, re2, lemax;
    mpfr_init2(rhp, PRECISION);
    mpfr_init2(redmax, PRECISION);
    mpfr_init2(redmax_re1, PRECISION);
    mpfr_init2(redmax_re2, PRECISION);
    mpfr_init2(re1max, PRECISION);
    mpfr_init2(re2max, PRECISION);
    mpfr_init2(re, PRECISION);
    mpfr_init2(re1, PRECISION);
    mpfr_init2(re2, PRECISION);
    mpfr_init2(lemax, PRECISION);
    
    
    mpfr_set_d(redmax, 0, MPFR_RNDN);
    mpfr_set_d(re1max, 0, MPFR_RNDN);
    mpfr_set_d(re2max, 0, MPFR_RNDN);
    mpfr_set_d(lemax, -100000, MPFR_RNDN);
    
    double dist = (nextafter(v, vend)) - v;
    
    for(int i = 0; i < 1000000; i ++){
        v= v + 0.0000001;
        
        double r1 = triton(v);
        double r2 = triton_ic(v);
        
        mpfr_float rhp_o = triton_hp(v);
        mpfr_float rhp_1 = triton_hp(nextafter(v, vend));
        rhp_1 = rhp_o - rhp_1;
        
        mpfr_t temp;
        mpfr_init2(temp, PRECISION);
        mpfr_set_d(temp, 0, MPFR_RNDN);
        
        mpfr_set(temp, rhp_1.backend().data(), GMP_RNDN);
        mpfr_abs(temp, temp, MPFR_RNDN);
        
        mpfr_set(rhp, rhp_o.backend().data(), GMP_RNDN);
        
        mpfr_sub_d(re1, rhp, r1, MPFR_RNDN);
        mpfr_abs(re1, re1, MPFR_RNDN);
        
        mpfr_sub_d(re2, rhp, r2, MPFR_RNDN);
        mpfr_abs(re2, re2, MPFR_RNDN);
        
        mpfr_sub(re, re1, re2, MPFR_RNDN);
        mpfr_abs(re, re, MPFR_RNDN);
        
        double tl = mpfr_get_d(rhp, MPFR_RNDD);
        double tu = mpfr_get_d(rhp, MPFR_RNDU);
        ulpd = tu - tl;
        
        mpfr_div_d(re, re, ulpd, MPFR_RNDN);
        mpfr_div_d(re1, re1, ulpd, MPFR_RNDN);
        mpfr_div_d(re2, re2, ulpd, MPFR_RNDN);
        mpfr_div_d(temp, temp, ulpd, MPFR_RNDN);
        
        if(mpfr_cmp(re, redmax) > 0){
            maxd = fabs(r1 - r2);
            
            mpfr_set(redmax, re, MPFR_RNDN);
            mpfr_set(redmax_re1, re1, MPFR_RNDN);
            mpfr_set(redmax_re2, re2, MPFR_RNDN);
        
            result1 = r1;
            result2 = r2;
            max_input = v;
        }
    
        if(mpfr_cmp(re1, re1max) > 0){
            mpfr_set(re1max, re1, MPFR_RNDN);
        }
        
        if(mpfr_cmp(re2, re2max) > 0){
            mpfr_set(re2max, re2, MPFR_RNDN);
        }
        
        if(mpfr_cmp(re1, re2) > 0){
            mpfr_add(temp, temp, re2, MPFR_RNDN);
            mpfr_sub(re, re, temp, MPFR_RNDN);
        }else{
            mpfr_add(temp, temp, re1, MPFR_RNDN);
            mpfr_sub(re, re, temp, MPFR_RNDN);
        }
        
        if(mpfr_cmp(re, lemax) > 0){
            mpfr_set(lemax, re, MPFR_RNDN);
        }
        
        if(i % 10000 == 0){
            printf("Iterations: %d\n", i);
            printf("Max Input %.17f\n", max_input);
            printf("Result %.17f\n", result1);
            printf("Result %.17f\n", result2);
            printf("ULP %.17f\n", ulpd);
            mpfr_printf("LEMAX %.128RNf\n", lemax);
            mpfr_printf("REDMAX %.128RNf\n", redmax);
            mpfr_printf("REDMAX_RE1 %.128RNf\n", redmax_re1);
            mpfr_printf("REDMAX_RE2 %.128RNf\n", redmax_re2);
            mpfr_printf("RE1MAX %.128RNf\n", re1max);
            mpfr_printf("RE2MAX %.128RNf\n", re2max);
        }
    }
    
    printf("Max Input %.17f\n", max_input);
    printf("Result %.17f\n", result1);
    printf("Result %.17f\n", result2);
    printf("ULP %.17f\n", ulpd);
    mpfr_printf("LEMAX %.128RNf\n", lemax);
    mpfr_printf("REDMAX %.128RNf\n", redmax);
    mpfr_printf("REDMAX_RE1 %.128RNf\n", redmax_re1);
    mpfr_printf("REDMAX_RE2 %.128RNf\n", redmax_re2);
    mpfr_printf("RE1MAX %.128RNf\n", re1max);
    mpfr_printf("RE2MAX %.128RNf\n", re2max);

    mpfr_clear(rhp);
    mpfr_clear(redmax);
    mpfr_clear(redmax_re1);
    mpfr_clear(redmax_re2);
    mpfr_clear(re1max);
    mpfr_clear(re2max);
    mpfr_clear(re);
    mpfr_clear(re1);
    mpfr_clear(re2);
}
