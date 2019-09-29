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

double set_ssat_elems(double jd){
    static const long semimaj[9] = { 268180L, 344301, 426393, 545876,
        762277, 1766041, 2140790, 5148431, 18720552 };
    static const short epoch[8] = { 11093, 11093, 11093, 11093, 11093, 11368,
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
    static const long big_P0[9] = { 106100, 309107, 0, 174800, 276590, 276590,
        69898, 352910, 280165 };
    static const long big_P0_dot[9] = { 36554900, 12344121, 0, 3082000,
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
    
    
    if( sat == PHOEBE)
    {
        elems->epoch = 2433282.5;
        elems->ecc = .16326;
    }
    else
    {
        elems->epoch = 2400000. + (double)epoch[sat];
        elems->ecc = (double)ecc0[sat] * 1.e-6;
        elems->gamma = (double)i_gamma0[sat] * (PI / 180.) / 10000.;
    }
    t_d = elems->jd - elems->epoch;
    t = t_d / 365.25;
    t_centuries = t / 100.;
    t_centuries_squared = t_centuries * t_centuries;
    if( sat == PHOEBE)
        elems->gamma = (173.949 - .020 * t) * (PI / 180.);
    
    elems->semimaj = (double)semimaj[sat] * SECONDS_TO_AU / 10000.;
    elems->lambda = (double)lam0[sat] / 10000. + n[sat] * t_d;
    elems->lambda *= PI / 180;          /* cvt to radians */
    elems->Omega = (double)big_N0[sat] / 1000. +
    t * (double)big_N0_dot[sat] / 100000.;
    elems->Omega *= PI / 180;          /* cvt to radians */
    
    elems->omega = (double)big_P0[sat] / 1000. +
    t * (double)big_P0_dot[sat] / 100000.;
    elems->omega *= PI / 180;          /* cvt to radians */
    
    switch( sat)
    {
        case MIMAS:
        case TETHYS:
        {
            const double libration_coeffs[3] = {-43.57 * PI / 180.,
                -.7209 * PI / 180., -.0205 * PI / 180. };
            const double mu0 = 5.095 * PI / 180.;
            const double t0_prime = 1866.39;
            const double mimas_over_tethys = -21.12;
            double mu_delta_tau = mu0 *
            ((elems->jd-J2000) / 365.25 + 2000. - t0_prime);
            int i;
            double delta_lon = 0.;
            
            for( i = 0; i < 3; i++)
                delta_lon += libration_coeffs[i] *
                sin( (double)(i+i+1) * mu_delta_tau);
            if( sat == TETHYS)
                delta_lon /= mimas_over_tethys;
            elems->lambda += delta_lon;
        }
            break;
            
        case ENCELADUS:
        case DIONE:
        {
            const double p2 = 15.4 * (PI / 180.) / 60.;
            const double q2 = 12.59 * (PI / 180.) / 60.;
            const double mu = 74.4 * (PI / 180.);
            const double nu = 32.39 * (PI / 180.);
            const double mu_prime = 134.3 * (PI / 180.);
            const double nu_prime = 92.62 * (PI / 180.);
            const double enceladus_over_dione = -12.;
            double delta_lon;
            
            delta_lon = p2 * sin( mu + nu * t) +
            q2 * sin( mu_prime + nu_prime * t);
            if( sat == DIONE)
                delta_lon /= enceladus_over_dione;
            elems->lambda += delta_lon;
        }
            break;
        case RHEA:
        {
            const double ef = .001;
            const double chi = .0193 * PI / 180.;
            const double pi0 = 342.7 * PI / 180.;
            const double pi_dot = 10.057 * PI / 180.;
            const double big_Nt0 = 42.02 * PI / 180.;
            const double big_Nt_dot = -.5118 * PI / 180.;
            const double Omega1_plus_dOmega = ASC_NODE0 - .0078 * PI / 180.;
            const double Incl1_plus_dIncl = INCL0 - .0455 * PI / 180.;
            const double e0 = .000265;
            
            const double pi = pi0 + pi_dot * t;
            const double big_N = elems->Omega;
            const double big_Nt = big_Nt0 + big_Nt_dot * t;
            const double e_sin_omega = e0 * sin( pi) + ef * sin( elems->omega);
            const double e_cos_omega = e0 * cos( pi) + ef * cos( elems->omega);
            double perturb_Omega, perturb_incl;
            
            double sinbigN = sin(elems->Omega);
            
            perturb_incl = sin_gamma0 * cos( big_N) + chi * cos( big_Nt);
            elems->gamma = Incl1_plus_dIncl + perturb_incl;
            perturb_Omega = sin_gamma0 * sinbigN + chi * sin( big_Nt);
            elems->Omega = Omega1_plus_dOmega + perturb_Omega / sin_incl1;
            elems->lambda += sin_gamma0_tan_half_incl * sinbigN;
            elems->omega = atan2( e_sin_omega, e_cos_omega);
            elems->ecc = sqrt( e_sin_omega*e_sin_omega +e_cos_omega*e_cos_omega);
        }
            break;
        case TITAN:
        {
            const double Omega1_plus_dOmega = ASC_NODE0 - .1420 * PI / 180.;
            const double Incl1_plus_dIncl = INCL0 - .6303 * PI / 180.;
            const double g0 = 103.199 * PI / 180.;
            const double beta = .3752 * PI / 180.;
            
            double g;
            
            double sinbigN = sin(elems->Omega);
            double cosbigN = cos(elems->Omega);
            
            double perturb_Omega, perturb_incl;
            
            elems->lambda += sin_gamma0_tan_half_incl * sinbigN;
            perturb_Omega = sin_gamma0 * sinbigN;
            elems->Omega = Omega1_plus_dOmega + perturb_Omega / sin_incl1;
            perturb_incl = sin_gamma0 * cosbigN;
            elems->gamma = Incl1_plus_dIncl + perturb_incl;
            g = elems->omega - elems->Omega - 4.6 * PI / 180.;
            elems->ecc += beta * elems->ecc * (cos( g + g) - cos( g0 + g0));
            elems->omega += beta * elems->ecc * (sin( g + g) - sin( g0 + g0));
        }
            break;
        case HYPERION:
        {
            const double tau0 =                   92.39 * PI / 180.;
            const double tau_dot =                  .5621071 * PI / 180.;
            const double zeta0 =                 148.19 * PI / 180.;
            const double zeta_dot =              -19.18 * PI / 180.;
            const double phi0 =                  -34.7 * PI / 180.;
            const double phi_dot =               -61.7840 * PI / 180.;
            const double theta0 =                184.8 * PI / 180.;
            const double theta_dot =             -35.41 * PI / 180.;
            const double theta0_prime =          177.3 * PI / 180.;
            const double theta_dot_prime =       -35.41 * PI / 180.;
            const double C_e_zeta =                 .02303;
            const double C_e_2zeta =               -.00212;
            const double C_lam_tau =               9.142 * PI / 180.;
            const double C_lam_zeta =              -.260 * PI / 180.;
            const double C_omega_zeta =          -12.872 * PI / 180.;
            const double C_omega_2zeta =           1.668 * PI / 180.;
            const double C_a_tau =                 -.00003509;
            const double C_a_zeta_plus_tau =       -.00000067;
            const double C_a_zeta_minus_tau =       .00000071;
            const double C_e_tau =                 -.004099;
            const double C_e_3zeta =                .000151;
            const double C_e_zeta_plus_tau =       -.000167;
            const double C_e_zeta_minus_tau =       .000235;
            const double C_lam_2zeta =             -.0098 * PI / 180.;
            const double C_lam_zeta_plus_tau =      .2275 * PI / 180.;
            const double C_lam_zeta_minus_tau =     .2112 * PI / 180.;
            const double C_lam_phi =               -.0303 * PI / 180.;
            const double C_omega_tau =             -.4457 * PI / 180.;
            const double C_omega_3zeta =           -.2419 * PI / 180.;
            const double C_omega_zeta_plus_tau =   -.2657 * PI / 180.;
            const double C_omega_zeta_minus_tau =  -.3573 * PI / 180.;
            const double C_incl_theta =             .0180 * PI / 180.;
            const double C_Omega_theta_prime =      .0168 * PI / 180.;
            const double big_Nt0 =                42.02 * PI / 180.;
            const double big_Nt_dot =              -.5118 * PI / 180.;
            const double hy_gamma0 =                .6435 * PI / 180.;
            const double sin_hy_gamma0 =             .011231;
            
            /* from (45), p 59 */
            const double Omega1_plus_dOmega =    ASC_NODE0 - .747 * PI / 180.;
            const double Incl1_plus_dIncl =          INCL0 - .13 * PI / 180.;
            /*       const double Omega1_plus_dOmega =    ASC_NODE0 - .0078 * PI / 180.; */
            /*       const double Incl1_plus_dIncl =          INCL0 - .0455 * PI / 180.; */
            const double sin_Incl1_plus_dIncl =        0.468727;
            const double tan_half_Incl1_plus_dIncl =   0.248880;
            
            /* from (44), p 59 */
            const double big_T = (elems->jd - 2442000.5) / 365.25;
            const double t_T = (elems->jd - 2411368.0) / 365.25;
            const double big_N = elems->Omega;
            const double big_Nt = big_Nt0 + big_Nt_dot * t_T;
            const double tau = tau0 + tau_dot * t_d;
            const double zeta = zeta0 + zeta_dot * t;
            const double phi = phi0 + phi_dot * t;
            const double lambda_s = (176. + 12.22 * t) * PI / 180.;
            const double b_s = (8. + 24.44 * t) * PI / 180.;
            const double d_s = b_s + 5. * PI / 180.;
            
            const double theta = theta0 + theta_dot * big_T;
            const double theta_prime = theta0_prime + theta_dot_prime * big_T;
            double arg;
            
            double sinbigN = sin(elems->Omega);
            
            elems->ecc = .103458;
            
            elems->gamma = sin_hy_gamma0 * cos( big_N)
            + .315 * (PI / 180.) * cos( big_Nt)
            - .018 * (PI / 180.) * cos( d_s)
            + C_incl_theta * cos( theta);
            elems->gamma += Incl1_plus_dIncl;
            
            arg = sinbigN;
            elems->Omega = sin_hy_gamma0 * arg
            + .315 * (PI / 180.) * sin( big_Nt)
            - .018 * (PI / 180.) * sin( d_s)
            + C_Omega_theta_prime * sin( theta_prime);
            elems->Omega = Omega1_plus_dOmega
            + elems->Omega / sin_Incl1_plus_dIncl;
            elems->lambda += hy_gamma0 * tan_half_Incl1_plus_dIncl * arg;
            elems->omega += hy_gamma0 * tan_half_Incl1_plus_dIncl * arg;
            arg = sin( tau);
            elems->lambda += C_lam_tau * arg
            + .007 * (PI / 180.) * sin( tau + tau)
            - .014 * (PI / 180.) * sin( 3. * tau)
            - .013 * (PI / 180.) * sin( lambda_s)
            + .017 * (PI / 180.) * sin( b_s)
            + C_lam_phi * sin( phi);
            elems->omega += C_omega_tau * arg
            + C_omega_3zeta * sin( 3. * zeta);
            arg = sin( zeta + tau);
            elems->lambda += C_lam_zeta_plus_tau * arg;
            elems->omega += C_omega_zeta_plus_tau * arg;
            arg = sin( zeta - tau);
            elems->lambda += C_lam_zeta_minus_tau * arg;
            elems->omega += C_omega_zeta_minus_tau * arg;
            arg = sin( zeta);
            elems->lambda += C_lam_zeta * arg;
            elems->omega += C_omega_zeta * arg;
            arg = sin( zeta + zeta);
            elems->lambda += C_lam_2zeta * arg;
            elems->omega += C_omega_2zeta * arg;
            
            arg = cos( tau);
            elems->semimaj += C_a_tau * arg * SECONDS_TO_AU;
            elems->ecc += C_e_tau * arg;
            arg = cos( zeta + tau);
            elems->semimaj += C_a_zeta_plus_tau * arg * SECONDS_TO_AU;
            elems->ecc += C_e_zeta_plus_tau * arg;
            arg = cos( zeta - tau);
            elems->semimaj += C_a_zeta_minus_tau * arg * SECONDS_TO_AU;
            elems->ecc += C_e_zeta_minus_tau * arg
            + C_e_zeta * cos( zeta)
            + C_e_2zeta * cos( zeta + zeta)
            + C_e_3zeta * cos( 3. * zeta)
            + .00013 * cos( phi);
        }
            break;
        case JAPETUS:
            elems->gamma = JAPETUS_i0 + JAPETUS_i0_dot * t_centuries;
            elems->gamma += (-.072 + .0054 * t_centuries) * t_centuries_squared
            * PI / 180.;
            elems->Omega += (.116 + .008 * t_centuries) * t_centuries_squared
            * PI / 180.;
            elems->ecc += .001156 * t_centuries;
            
            /* The following corrections are from p. 61, */
            /* G. Dourneau,  group 50: */
        {
            const double big_T = (elems->jd - 2415020.) / 36525.;
            const double t_diff = elems->jd - 2411368.;
            const double lam_s =         (267.263 + 1222.114 * big_T) * (PI / 180.);
            const double omega_s_tilde = ( 91.796 +     .562 * big_T) * (PI / 180.);
            const double psi =           (  4.367 -     .195 * big_T) * (PI / 180.);
            const double theta =         (146.819 -    3.918 * big_T) * (PI / 180.);
            const double lam_t =         (261.319 + 22.576974 * t_diff) * (PI / 180.);
            const double omega_t_tilde = (277.102 +   .001389 * t_diff) * (PI / 180.);
            const double phi =           ( 60.470 +    1.521 * big_T) * (PI / 180.);
            const double Phi =           (205.055 -    2.091 * big_T) * (PI / 180.);
            
            /* group 49: */
            const double l = elems->lambda - elems->omega;
            const double g  = elems->omega - elems->Omega - psi;
            const double g1 = elems->omega - elems->Omega - phi;
            const double ls = lam_s - omega_s_tilde;
            const double gs = omega_s_tilde - theta;
            const double lt = lam_t - omega_t_tilde;
            const double gt = omega_t_tilde - Phi;
            const double ls_plus_gs_2 = 2. * (ls + gs);
            const double ls_gs_minus_g_2 = ls_plus_gs_2 - 2. * g;
            const double lt_plus_gt = lt + gt;
            const double lt_gt_minus_g1 = lt_plus_gt - g1;
            
            
            /* group 48: */
            const double d_a = elems->semimaj * (7.87 * cos( 2. * l - ls_gs_minus_g_2)
                                                 + 98.79 * cos( l - lt_gt_minus_g1));
            const double d_e = -140.97 * cos( g1 - gt)
            + 37.33 * cos( ls_gs_minus_g_2)
            + 11.80 * cos( l - ls_gs_minus_g_2)
            + 24.08 * cos( l)
            + 28.49 * cos( l + l - lt_gt_minus_g1)
            + 61.90 * cos( lt_gt_minus_g1);
            const double d_omega = .08077 * sin( g1 - gt)
            + .02139 * sin( ls_gs_minus_g_2)
            - .00676 * sin( l - ls_gs_minus_g_2)
            + .01380 * sin( l)
            + .01632 * sin( l + l - lt_gt_minus_g1)
            + .03547 * sin( lt_gt_minus_g1);
            const double d_lambda = -.04299 * sin( l - lt_gt_minus_g1)
            -.00789 * sin( 2. * l - ls_gs_minus_g_2)
            -.06312 * sin( ls)
            -.00295 * sin( ls + ls)
            -.02231 * sin( ls_plus_gs_2)
            +.00650 * sin( ls_plus_gs_2 + phi);
            const double d_incl = .04204 * cos( ls_plus_gs_2 + phi)
            +.00235 * cos( l + g1 + lt_plus_gt + phi)
            +.00360 * cos( l - lt_gt_minus_g1 + phi);
            const double d_Omega = .04204 * sin( ls_plus_gs_2 + phi)
            +.00235 * sin( l + g1 + lt_plus_gt + phi)
            +.00358 * sin( l - lt_gt_minus_g1 + phi);
            
            elems->semimaj += d_a * 1.e-5;
            elems->omega += d_omega * (PI / 180.) / elems->ecc;
            elems->Omega += d_Omega * (PI / 180.) / sin( elems->gamma);
            elems->ecc += d_e * 1.e-5;
            elems->lambda += d_lambda * (PI / 180.);
            elems->gamma += d_incl * (PI / 180.);
        }
            break;
        case PHOEBE:
            /* The elements given for Phoebe in the     */
            /* _Explanatory Suppl_ run the 'wrong way'. */
            /* Either the retrograde orbit confused them,  */
            /* or they chose to swap conventions. */
            elems->lambda = 2. * elems->Omega - elems->lambda;
            elems->omega  = 2. * elems->Omega - elems->omega;
            break;
        default:
            break;
    }
    
    if( sat < RHEA)
    {
        elems->Omega -= ASC_NODE0;
        elems->omega -= ASC_NODE0;
        elems->lambda -= ASC_NODE0;
    }
    
    orbit->mean_anomaly = elems->lambda - elems->omega;
    //   orbit->mean_anomaly = fmod( orbit->mean_anomaly, TWO_PI);
    //   if( orbit->mean_anomaly > PI)
    //      orbit->mean_anomaly -= TWO_PI;
    //   if( orbit->mean_anomaly <-PI)
    //      orbit->mean_anomaly += TWO_PI;
    
    orbit->major_axis = elems->semimaj;
    orbit->q = elems->semimaj * (1. - elems->ecc);
    orbit->ecc = elems->ecc;
    orbit->incl = elems->gamma;
    orbit->arg_per = elems->omega - elems->Omega;
    orbit->asc_node = elems->Omega;
//
    return orbit -> arg_per;
}

