#include <stdio.h>
#include <mpfr.h>
#include <math.h>


#include <boost/multiprecision/mpfr.hpp>

using namespace boost::multiprecision;
#define PRECISION 256

double ex6(double t, double sigma_, double kappa_, double rho_, double v0_,  double theta_);
double ex6_ic(double t, double sigma_, double kappa_, double rho_, double v0_,  double theta_);

mpfr_float ex6_hp(mpfr_float t){
    mpfr_float sigma_ = 0.3;
    mpfr_float kappa_ = -0.3;
    mpfr_float rho_ = 0.1;
    mpfr_float v0_ = 1.5;
    mpfr_float theta_ = 0.1;
    mpfr_float sigma2 = sigma_*sigma_;
    mpfr_float sigma3 = sigma2*sigma_;
    mpfr_float sigma4 = sigma2*sigma2;
    mpfr_float kappa2 = kappa_*kappa_;
    mpfr_float kappa3 = kappa2*kappa_;
    mpfr_float kappa4 = kappa2*kappa2;
    mpfr_float kappa5 = kappa2*kappa3;
    mpfr_float kappa6 = kappa3*kappa3;
    mpfr_float kappa7 = kappa4*kappa3;
    mpfr_float rho2 = rho_*rho_;
    mpfr_float rho3 = rho2*rho_;
    mpfr_float t2 = t*t;
    mpfr_float t3 = t2*t;
    return
    (sigma2*(3*sigma4*(theta_ - 4*v0_) +
             3*exp(4*kappa_*t)*((-93*sigma4 +
                                 64*kappa5*(t + 4*rho2*t) +
                                 4*kappa_*sigma3*(176*rho_ + 5*sigma_*t) -
                                 32*kappa2*sigma2*(11 + 50*rho2 +
                                                   5*rho_*sigma_*t) + 32*kappa3*sigma_*(3*sigma_*t + 4*rho_*(10 +
                                                                                                             8*rho2 + 3*rho_*sigma_*t)) - 32*kappa4*(5 +
                                                                                                                                                     4*rho_*(6*rho_ + (3 + 2*rho2)*sigma_*t)))*theta_ +
                                4*(4*kappa2 - 4*kappa_*rho_*sigma_ +
                                   sigma2)*(4*kappa2*(1 + 4*rho2) -
                                            20*kappa_*rho_*sigma_ + 5*sigma2)*v0_) +
             24*exp(kappa_*t)*sigma2*(-2*kappa2*(-1 +
                                                 rho_*sigma_*t)*(theta_ - 3*v0_) + sigma2*(theta_ - 2*v0_) +
                                      kappa_*sigma_*(-4*rho_*theta_ + sigma_*t*theta_ + 10*rho_*v0_ -
                                                     3*sigma_*t*v0_)) + 12*exp(2*kappa_*t)*(sigma4*(7*theta_ -
                                                                                                    4*v0_) + 8*kappa4*(1 + 2*rho_*sigma_*t*(-2 +
                                                                                                                                            rho_*sigma_*t))*(theta_ - 2*v0_) +
                                                                                            2*kappa_*sigma3*(-24*rho_*theta_ + 5*sigma_*t*theta_ +
                                                                                                             20*rho_*v0_ - 6*sigma_*t*v0_) + 4*kappa2*sigma2*((6
                                                                                                                                                               + 20*rho2 - 14*rho_*sigma_*t +
                                                                                                                                                               sigma2*t2)*theta_ - 2*(3 + 12*rho2 -
                                                                                                                                                                                      10*rho_*sigma_*t + sigma2*t2)*v0_) +
                                                                                            8*kappa3*sigma_*((3*sigma_*t + 2*rho_*(-4 + sigma_*t*(4*rho_ -
                                                                                                                                                  sigma_*t)))*theta_ + 2*(-3*sigma_*t + 2*rho_*(3 + sigma_*t*(-3*rho_ +
                                                                                                                                                                                                              sigma_*t)))*v0_)) -
             8*exp(3*kappa_*t)*(16*kappa6*rho2*t2*(-3 + rho_*sigma_*t)*(theta_ - v0_) - 3*sigma4*(7*theta_ +
                                                                                                  2*v0_) + 2*kappa3*sigma_*((192*(rho_ + rho3) -
                                                                                                                             6*(9 + 40*rho2)*sigma_*t + 42*rho_*sigma2*t2 -
                                                                                                                             sigma3*t3)*theta_ + (-48*rho3 + 18*(1
                                                                                                                                                                 + 4*rho2)*sigma_*t - 24*rho_*sigma2*t2
                                                                                                                                                  + sigma3*t3)*v0_) + 12*kappa4*((-4 -
                                                                                                                                                                                  24*rho2 + 8*rho_*(4 + 3*rho2)*sigma_*t - (3 +
                                                                                                                                                                                                                            14*rho2)*sigma2*t2 + rho_*sigma3*t3)*theta_ + (8*rho2 -
                                                                                                                                                                                                                                                                           8*rho_*(2 + rho2)*sigma_*t + (3 +
                                                                                                                                                                                                                                                                                                         8*rho2)*sigma2*t2 - rho_*sigma3*t3)*v0_) -
                                6*kappa2*sigma2*((15 + 80*rho2 -
                                                  35*rho_*sigma_*t + 2*sigma2*t2)*theta_ + (3 +
                                                                                            sigma_*t*(7*rho_ - sigma_*t))*v0_) + 24*kappa5*t*((-2 +
                                                                                                                                               rho_*(4*sigma_*t + rho_*(-8 + sigma_*t*(4*rho_ - sigma_*t))))*theta_ + (2 +
                                                                                                                                                                                                                       rho_*(-4*sigma_*t + rho_*(4 + sigma_*t*(-2*rho_ + sigma_*t))))*v0_) +
                                3*kappa_*sigma3*(sigma_*t*(-9*theta_ + v0_) + 10*rho_*(6*theta_
                                                                                       + v0_)))))/(64.*exp(4*kappa_*t)*kappa7);
}


int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 1; //-4.5;
    double vend= 10;//-0.3;
    
    double v = vbegin;
    
    double sigma_ = 0.3;
    double kappa_ = -0.3;
    double rho_ = 0.1;
    double v0_ = 1.5;
    double theta_ = 0.1;
    
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
    
    for(int i = 0; i < 100000; i ++){
        v= v + 0.0001;
        double r1 = ex6(v, sigma_, kappa_, rho_, v0_, theta_);
        double r2 = ex6_ic(v, sigma_, kappa_, rho_, v0_, theta_);
        mpfr_float b = ex6_hp(v);
        
        mpfr_set(rhp, b.backend().data(), GMP_RNDN);
        mpfr_float rhp_1 = ex6_hp(nextafter(v, vend));
        rhp_1 = b - rhp_1;
        
        mpfr_t temp;
        mpfr_init2(temp, PRECISION);
        mpfr_set_d(temp, 0, MPFR_RNDN);
        
        mpfr_set(temp, rhp_1.backend().data(), GMP_RNDN);
        mpfr_abs(temp, temp, MPFR_RNDN);
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
        
        mpfr_div(re1, re1, temp, MPFR_RNDN);
        mpfr_div(re2, re2, temp, MPFR_RNDN);
        
        mpfr_sub(re, re1, re2, MPFR_RNDN);
        mpfr_abs(re, re, MPFR_RNDN);
        
        if(mpfr_cmp(re, lemax) > 0){
            mpfr_set(lemax, re, MPFR_RNDN);
        }
    }

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

