#include <stdio.h>
#include <math.h>
#include <mpfr.h>

#define PRECISION 256
#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

double ex6(double v);
double ex6_ic(double v);

void ex6_hp(double jd, mpfr_t x){
    mpfr_t tcent_mf, nmf, theta_mf, long_mf, gamma_mf;
    
    mpfr_init2(tcent_mf, PRECISION);
    mpfr_init2(nmf, PRECISION);
    mpfr_init2(theta_mf, PRECISION);
    mpfr_init2(long_mf, PRECISION);
    mpfr_init2(gamma_mf, PRECISION);
    
    //    mpfr_set_d(tcent_mf, jd, MPFR_RNDN);
    //    mpfr_sub_d(tcent_mf, tcent_mf, J2000, MPFR_RNDN);
    //    mpfr_div_d(tcent_mf, tcent_mf, 36525., MPFR_RNDN);
    //
    //    mpfr_mul_d(nmf, tcent_mf, 54.308, MPFR_RNDN);
    //    mpfr_add_d(nmf, nmf, 359.28, MPFR_RNDN);
    
    mpfr_set_d(theta_mf, jd, MPFR_RNDN);
    mpfr_sub_d(theta_mf, theta_mf, 2433282.5, MPFR_RNDN);
    mpfr_mul_d(theta_mf, theta_mf, .57806, MPFR_RNDN);
    mpfr_div_d(theta_mf, theta_mf, 365.25, MPFR_RNDN);
    mpfr_add_d(theta_mf, theta_mf, 151.401, MPFR_RNDN);
    mpfr_mul_d(theta_mf, theta_mf, PI, MPFR_RNDN);
    mpfr_div_d(theta_mf, theta_mf, 180., MPFR_RNDN);
    
    mpfr_set_d(long_mf, jd, MPFR_RNDN);
    mpfr_sub_d(long_mf, long_mf, 2433282.5, MPFR_RNDN);
    mpfr_mul_d(long_mf, long_mf, 61.2588532, MPFR_RNDN);
    mpfr_add_d(long_mf, long_mf, 200.913, MPFR_RNDN);
    mpfr_mul_d(long_mf, long_mf, PI, MPFR_RNDN);
    mpfr_div_d(long_mf, long_mf, 180., MPFR_RNDN);
    
    mpfr_set_d(gamma_mf, PI, MPFR_RNDN);
    mpfr_div_d(gamma_mf, gamma_mf, 180., MPFR_RNDN);
    mpfr_mul_d(gamma_mf, gamma_mf, 158.996, MPFR_RNDN);
    
    mpfr_sin(tcent_mf, long_mf, MPFR_RNDN);
    mpfr_cos(gamma_mf, gamma_mf, MPFR_RNDN);
    mpfr_mul(tcent_mf, tcent_mf, gamma_mf, MPFR_RNDN);
    mpfr_cos(nmf, long_mf, MPFR_RNDN);
    mpfr_atan2(x, tcent_mf, nmf, MPFR_RNDN);
    mpfr_add(x, x, theta_mf, MPFR_RNDN);
    
    
    mpfr_clear(tcent_mf);
    mpfr_clear(nmf);
    mpfr_clear(theta_mf);
    mpfr_clear(long_mf);
    mpfr_clear(gamma_mf);
    
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 100;
    double vend= 101;
    
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
    
    double v = vbegin;
    
    // double dist = (nextafter(v, vend)) - v;
    
    for(int i = 0; i < 1000000; i ++){
        v =  v + 0.000001;
        
        double r1 = ex6(v);
        double r2 = ex6_ic(v);
        
        mpfr_set_d(rhp, 0, MPFR_RNDN);
        ex6_hp(v, rhp);
        
        mpfr_t temp;
        mpfr_init2(temp, PRECISION);
        mpfr_set_d(temp, 0, MPFR_RNDN);
        ex6_hp(nextafter(v, vend), temp);
        mpfr_sub(temp, temp, rhp, MPFR_RNDN);
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




