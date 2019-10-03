#include <math.h>

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
namespace  {
    
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
        double perih_time, q, ecc, incl, arg_per, asc_node;
        double epoch,  mean_anomaly;
        /* derived quantities: */
        double lon_per, minor_to_major;
        double perih_vec[3], sideways[3];
        double angular_momentum, major_axis, t0, w0;
        double abs_mag, slope_param, gm;
        int is_asteroid, central_obj;
    };
    
#define SAT_ELEMS struct sat_elems
    
    SAT_ELEMS
    {
        double jd, semimaj, ecc, gamma, lambda;
        double omega, Omega, epoch;
        double loc[4];
        int sat_no;
    };
}
#define sat 7
double set_ssat_elems(double jd){
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
    static double n[9] = { 381.994497, 262.7319002, 190.69791226,
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
    double sin_gamma0_tan_half_incl = .00151337;
    double sin_gamma0 = .0060545;
    double sin_incl1 = .470730;
    double t, t_d, t_centuries, t_centuries_squared;
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

    const double big_T = (elems->jd - 2415020.) / 36525.;
    const double t_diff = elems->jd - 2411368.;
    const double lam_s =         (267.263 + 1222.114 * big_T) * (PI / 180.);
    const double omega_s_tilde = ( 91.796 +     .562 * big_T) * (PI / 180.);
    const double psi =           (  4.367 -     .195 * big_T) * (PI / 180.);
    const double theta =         (146.819 -    3.918 * big_T) * (PI / 180.);
    const double lam_t =         (261.319 + 22.576974 * t_diff)* (PI / 180.);
    const double omega_t_tilde = (277.102 +   .001389 * t_diff)* (PI / 180.);
    const double phi =           ( 60.470 +    1.521 * big_T) * (PI / 180.);
    const double Phi =           (205.055 -    2.091 * big_T)* (PI / 180.);
    const double phi_minus_Phi = (-144.585 +    3.612 * big_T)* (PI / 180.);
    const double ls = (175.467 + 1221.552 * big_T) * (PI / 180.);
    const double gs = (-55.023 +     4.48 * big_T) * (PI / 180.);
    const double lt = (-15.783 + 22.575585 * t_diff) * (PI / 180.);
    const double lam_s_minus_theta =  (120.444 + 1226.032 * big_T) * (PI / 180.);
    const double lam_s_minus_theta_plus_psi =  (124.811 + 1225.837 * big_T) * (PI / 180.);
    
    const double l = elems->lambda - elems->omega;
    const double g  = elems->omega - elems->Omega - psi;
    const double g1 = elems->omega - elems->Omega - phi;
    const double gt = omega_t_tilde - Phi;

    const double ls_plus_gs_2 =  2. * lam_s_minus_theta;
    const double ls_gs_minus_g_2 = 2 * (lam_s_minus_theta_plus_psi + elems->Omega - elems->omega);
    const double lt_plus_gt = lam_t - Phi;
    const double lt_gt_minus_g1 = lam_t + elems->Omega + phi_minus_Phi - elems->omega;
    
    return cos(elems->lambda- lam_s_minus_theta_plus_psi - elems->Omega);
}
