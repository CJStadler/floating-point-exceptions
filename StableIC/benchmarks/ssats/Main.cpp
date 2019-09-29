#include <stdio.h>
#include <mpfr.h>
#include <math.h>


#include <boost/multiprecision/mpfr.hpp>

using namespace boost::multiprecision;
#define PRECISION 256


double set_ssat_elems_ic(double jd);
double set_ssat_elems(double jd);

/*
 All references are from G. Dourneau unless otherwise noted.
 
 The Phoebe orbital elements are from the _Explanatory Supplement to
 the Astronomical Almanac_,  and should not be trusted very much;  they
 are horribly outdated,  and don't match reality very well at all.
 They are not actually used in any of my code.
 
 There are a few places to look for alternative algorithms/code for the
 satellites of Saturn.  Peter Duffett-Smith's book "Practical Astronomy
 with your Calculator" provides a simpler theory,  with mostly circular
 orbits,  and Dan Bruton has implemented this in BASIC code in his
 SATSAT2 program.  At the other extreme,  the Bureau des Longitudes
 (http://www.bdl.fr) provides Fortran code implementing the TASS 1.7
 theory,  the successor to the Dourneau theory used in the following
 code.  TASS probably supplies slightly better accuracy than the
 Dourneau theory,  but you would have to be looking well below the
 arcsecond level to see much difference.
 
 None of these provides good data for Phoebe.  If you're really interested
 in Phoebe,  let me know;  I can provide the source code used in Guide for
 Phoebe (and the other irregular satellites of gas giants).  It uses
 multipoint interpolation in precomputed ephemerides,  resulting in
 wonderful accuracy.  (The precomputed ephemeris resulted from a
 numerically integrated orbit.)
 
 'htc20.cpp' provides ephemerides for Helene,  Telesto,  and Calypso.
 'rocks.cpp' provides ephemerides for many other faint inner satellites
 of Saturn (and other planets).
 */

#define PI 3.1415926535897932384626433832795028841971693993751058209749445923
#define TWO_PI (2. * PI)
#define J2000 2451545.

#define OBLIQUITY_1950 (23.445792 * PI / 180.)
/* Constants defining the angle of a 'fixed' Saturnian equator */
/* relative to the B1950.0 ecliptic.  The inner four moons are */
/* all computed relative to the plane of Saturn's equator; you */
/* then rotate by these two angles, and you're in B1950.0      */
/* ecliptic coordinates.  (The outer four moons are all in that */
/* system to begin with.)        */
#define INCL0 (28.0817 * PI / 180.)
#define ASC_NODE0 (168.8112 * PI / 180.)

#define JAPETUS_i0         (18.4602 * PI / 180.)
#define JAPETUS_i0_dot     (-.9518 * PI / 180.)

#define IGNORED_DOUBLE     0.

#define MIMAS           0
#define ENCELADUS       1
#define TETHYS          2
#define DIONE           3
#define RHEA            4
#define TITAN           5
#define HYPERION        6
#define JAPETUS         7
#define PHOEBE          8

#define SECONDS_TO_AU (9.538937 * (PI / 180.) / 3600.)

#define THRESH 1.e-12
#define MIN_THRESH 1.e-14
#define CUBE_ROOT( X)  (exp( log( X) / 3.))

#define ELEMENTS struct elements
ELEMENTS
{
    mpfr_float perih_time, q, ecc, incl, arg_per, asc_node;
    mpfr_float epoch,  mean_anomaly;
    /* derived quantities: */
    mpfr_float lon_per, minor_to_major;
    mpfr_float perih_vec[3], sideways[3];
    mpfr_float angular_momentum, major_axis, t0, w0;
    mpfr_float abs_mag, slope_param, gm;
    int is_asteroid, central_obj;
};

#define SAT_ELEMS struct sat_elems

SAT_ELEMS
{
    mpfr_float jd, semimaj, ecc, gamma, lambda;
    mpfr_float omega, Omega, epoch;
    mpfr_float loc[4];
    int sat_no;
};

#define sat 7
/* set_ssat_elems( ) is the core part of computing positions for the
 satellites of Saturn,  and quite probably the only part of the code
 you'll want to grab.  It is essentially just an implementation of
 Gerard Dourneau's theory.  The only problem with this theory is that
 each satellite has to be handled a little differently... thus the extensive
 case statement in this function.  The result,  though,  is a set of
 orbital elements for the object.  For the inner four moons,  this is
 relative to the equator of Saturn,  and you have to do two rotations to
 get a B1950.0 coordinate.  For the outer four moons,  you get B1950.0
 elements right away. */

mpfr_float set_ssat_elems_hp(mpfr_float jd){
    static const long semimaj[9] = { 268180L, 344301, 426393, 545876,
        762277, 1766041, 2140790, 5148431, 18720552 };
    double epoch[8] = { 11093, 11093, 11093, 11093, 11093, 11368,
        15020, 9786 };
    static const short ecc0[8] = { 19050, 4850, 0, 2157, 265, 29092, -1,
        28298   /*, 163260 */ };
    static const short i_gamma0[8] = { 15630, 262, 10976, 139,
        3469, 2960, 6435, -1 };
    static const long lam0[9] = {1276400, 2003170, 2853060, 2547120, 3592440,
        2611582, 1770470, 763852, 2778720 };
    static mpfr_float n[9] = { 381.994497, 262.7319002, 190.69791226,
        131.53493193, 79.6900472, 22.57697855,
        16.91993829, 4.53795125, -.6541068 };
    static const long big_N0[9] = { 54500, 348000, 111330, 232000, 345000,
        42000, 94900, 143198, 245998 };
    static const long big_N0_dot[9] = { -36507200, -15195000, -7224410,
        -3027000, -1005700, -51180, -229200, -3919, -41353 };
    double big_P0[9] = { 106100, 309107, 0, 174800, 276590, 276590,
        69898, 352910, 280165 };
    double big_P0_dot[9] = { 36554900, 12344121, 0, 3082000,
        51180, 51180, -1867088, 11710, -19586 };
    mpfr_float sin_gamma0_tan_half_incl = .00151337;
    mpfr_float sin_gamma0 = .0060545;
    mpfr_float sin_incl1 = .470730;
    mpfr_float t, t_d, t_centuries, t_centuries_squared;
    SAT_ELEMS oelems;
    ELEMENTS oorbit;
    
    SAT_ELEMS *elems = &oelems;
    ELEMENTS *orbit = &oorbit;
    elems -> jd = jd;
    elems->epoch = 2400000. + (double)epoch[sat];
    elems->ecc = (double)ecc0[sat] * 1.e-6;
    elems->gamma = (double)i_gamma0[sat] * (PI / 180.) / 10000.;
    t_d = elems->jd - elems->epoch;
    t = t_d / 365.25;
    t_centuries = t / 100.;
    t_centuries_squared = t_centuries * t_centuries;

    elems->semimaj = (double)semimaj[sat] * SECONDS_TO_AU / 10000.;
    elems->lambda = (double)lam0[sat] / 10000. + n[sat] * t_d;
    elems->lambda *= PI / 180;          /* cvt to radians */
    elems->Omega = (double)big_N0[sat] / 1000. +
    t * (double)big_N0_dot[sat] / 100000.;
    elems->Omega *= PI / 180;          /* cvt to radians */
    
    elems->omega = (double)big_P0[sat] / 1000. +
    t * (double)big_P0_dot[sat] / 100000.;
    
    elems->omega *= PI / 180;          /* cvt to radians */
   
            elems->gamma = JAPETUS_i0 + JAPETUS_i0_dot * t_centuries;
            elems->gamma += (-.072 + .0054 * t_centuries) * t_centuries_squared
            * PI / 180.;
    
            elems->Omega += (.116 + .008 * t_centuries) * t_centuries_squared
            * PI / 180.;
            elems->ecc += .001156 * t_centuries;
            /* The following corrections are from p. 61, */
            /* G. Dourneau,  group 50: */
        {
            const mpfr_float big_T = (elems->jd - 2415020.) / 36525.;
            const mpfr_float t_diff = elems->jd - 2411368.;
            const mpfr_float lam_s =         (267.263 + 1222.114 * big_T) * (PI / 180.);
            const mpfr_float omega_s_tilde = ( 91.796 +     .562 * big_T) * (PI / 180.);
            const mpfr_float psi =           (  4.367 -     .195 * big_T) * (PI / 180.);
            const mpfr_float theta =         (146.819 -    3.918 * big_T) * (PI / 180.);
            const mpfr_float lam_t =         (261.319 + 22.576974 * t_diff)* (PI / 180.);
            const mpfr_float omega_t_tilde = (277.102 +   .001389 * t_diff) * (PI / 180.);
            const mpfr_float phi =           ( 60.470 +    1.521 * big_T) * (PI / 180.);
            const mpfr_float Phi =           (205.055 -    2.091 * big_T) * (PI / 180.);
            const mpfr_float phi_minus_Phi = (-144.585 +    3.612 * big_T) * (PI / 180.);
            const mpfr_float ls = (175.467 + 1221.552 * big_T) * (PI / 180.);
            const mpfr_float gs = (-55.023 +     4.48 * big_T) * (PI / 180.);
            const mpfr_float lt = (-15.783 + 22.575585 * t_diff) * (PI / 180.);
            const mpfr_float lam_s_minus_theta =  (120.444 + 1226.032 * big_T) * (PI / 180.);
            const mpfr_float lam_s_minus_theta_plus_psi =  (124.811 + 1225.837 * big_T) * (PI / 180.);
            
            /* group 49: */
            const mpfr_float l = elems->lambda - elems->omega;
            const mpfr_float g  = elems->omega - elems->Omega - psi;
            const mpfr_float g1 = elems->omega - elems->Omega - phi;
            const mpfr_float gt = omega_t_tilde - Phi;
   
            const mpfr_float ls_plus_gs_2 = 2. * (lam_s - theta);
            const mpfr_float ls_gs_minus_g_2 = ls_plus_gs_2 - 2. * g;
            const mpfr_float lt_plus_gt = lam_t - Phi;
            const mpfr_float lt_gt_minus_g1 = lam_t + elems->Omega + phi - Phi - elems->omega;

            return cos(elems->lambda- lam_s_minus_theta_plus_psi - elems->Omega);
            /* group 48: */
            const mpfr_float d_a = elems->semimaj * ( 7.87 * cos( 2. * l - ls_gs_minus_g_2)
                                    //+98.79 * cos(l + Phi +  elems->omega - lam_t - elems->Omega - phi)
                                                     );
 
            
           const mpfr_float d_e = //-140.97 * cos( g1 - gt)
//            + 37.33 * cos( ls_gs_minus_g_2)
//            + 11.80 * cos( l - ls_gs_minus_g_2)
            24.08 * cos( l);
//            + 28.49 * cos(2*l +  Phi +  elems->omega - lam_t - elems->Omega - phi)
//            + 61.90 * cos( lt_gt_minus_g1);

            
            const mpfr_float d_omega = //.08077 * sin( g1 - gt)
        //    + .02139 * sin( ls_gs_minus_g_2)
                     //   - .00676 * sin( l - ls_gs_minus_g_2)
            .01380 * sin( l);
           // + .01632 * sin( 2*l +  Phi +  elems->omega - lam_t - elems->Omega - phi)+
          //  .03547 * sin( lt_gt_minus_g1);
    
            const mpfr_float d_lambda =// -.04299 * sin( l - lt_gt_minus_g1)
           // -.00789 * sin( 2. * l - ls_gs_minus_g_2)
            -.06312 * sin( ls);
           // -.00295 * sin( ls + ls)
          //  -.02231 * sin( ls_plus_gs_2)
          //  +.00650 * sin( ls_plus_gs_2 + phi);
            
//            const mpfr_float d_incl = .04204 * cos( ls_plus_gs_2 + phi)
//            +.00235 * cos( l + g1 + lt_plus_gt + phi)
//            +.00360 * cos( l - lt_gt_minus_g1 + phi);
//
            const mpfr_float d_Omega = .04204 * sin( ls_plus_gs_2 + phi);
//            +.00235 * sin( l + g1 + lt_plus_gt + phi);
//            +.00358 * sin( l - lt_gt_minus_g1 + phi);
         
            
            elems->semimaj += d_a * 1.e-5;
            elems->omega += d_omega * (PI / 180.) / elems->ecc;
            elems->Omega += d_Omega * (PI / 180.) / sin( elems->gamma);
            elems->ecc += d_e * 1.e-5;
            elems->lambda += d_lambda * (PI / 180.);
//            elems->gamma += d_incl * (PI / 180.);

        }
}


int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 10;
    double vend= 10.1;
    
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
    
    for(int i = 0; i < 10000; i ++){
        v= v + 0.00001;
        //v = 100.06026599984784298;
        
        double r1 = set_ssat_elems(v);
        
        double r2 = set_ssat_elems_ic(v);
        mpfr_float rhp_o= set_ssat_elems_hp(v);
        mpfr_float rhp_1 = set_ssat_elems_hp(nextafter(v, vbegin));
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
        //
        double tl = mpfr_get_d(rhp, MPFR_RNDD);
        double tu = mpfr_get_d(rhp, MPFR_RNDU);
        ulpd = tu - tl;
        
        mpfr_div_d(re, re, ulpd, MPFR_RNDN);
        mpfr_div_d(re1, re1, ulpd, MPFR_RNDN);
        mpfr_div_d(re2, re2, ulpd, MPFR_RNDN);
        mpfr_div_d(temp, temp, ulpd, MPFR_RNDN);
        
        if(mpfr_cmp_d(temp, 1) < 0){
            mpfr_set_d(temp, 1, MPFR_RNDN);
        }
        
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
        
        mpfr_div(re1, re1, temp, MPFR_RNDN);
        mpfr_div(re2, re2, temp, MPFR_RNDN);
        
        mpfr_sub(re, re1, re2, MPFR_RNDN);
        mpfr_abs(re, re, MPFR_RNDN);
        
        
        
        if(mpfr_cmp(re, lemax) > 0){
            mpfr_set(lemax, re, MPFR_RNDN);
            mpfr_printf("Rounding Error of Unoptimized Program: %.2RNf\n", re1);
            mpfr_printf("Rounding Error of Optimized Program: %.2RNf\n", re2);
        }
        
        
    }
    printf("Input: %.17f\n", max_input);
    mpfr_printf("Max Rounding Error of Unoptimized Program: %.2RNf\n", re1max);
    mpfr_printf("Max Rounding Error of Optimized Program: %.2RNf\n", re2max);
    mpfr_printf("Max Rounding Error Difference: %.2RNf\n", redmax);
    mpfr_printf("c: %.2RNf\n", lemax);
    
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

