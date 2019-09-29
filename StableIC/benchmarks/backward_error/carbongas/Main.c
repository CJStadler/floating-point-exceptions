#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <mpfr.h>


#define PRECISION 256

double ex11(double v);
double ex11_ic(double v);

void ex11_hp(double v, mpfr_t vmf){
    double p = 35000000.0;
    double a = 0.401;
    double b = 4.27e-05;
    double t = 300.0;
    double n = 1000.0;
    double k = 1.3806503e-23;
    
    mpfr_t tmp1, tmp2;
    
    mpfr_init2(tmp1, PRECISION);
    mpfr_init2(tmp2, PRECISION);
    
    mpfr_set_d(tmp1, n, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, b, MPFR_RNDN);
    mpfr_d_sub(tmp1, v, tmp1, MPFR_RNDN);
   
    
    mpfr_set_d(tmp2, n, MPFR_RNDN);
    mpfr_div_d(tmp2, tmp2, v, MPFR_RNDN);
    mpfr_mul(tmp2, tmp2, tmp2, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, a, MPFR_RNDN);
    mpfr_add_d(tmp2, tmp2, p, MPFR_RNDN);
    
    mpfr_mul(tmp1, tmp1, tmp2, MPFR_RNDN);
  
    mpfr_set_d(tmp2, k, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, n, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, t, MPFR_RNDN);
    
    mpfr_sub(vmf, tmp1, tmp2, MPFR_RNDN);
    
    mpfr_clear(tmp1);
    mpfr_clear(tmp2);
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 1;
    double vend= 10;
    
    double v = vbegin;
    
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
        v= v + 0.00009;

        double r1 = ex11(v);
        double r2 = ex11_ic(v);
        
        mpfr_set_d(rhp, 0, MPFR_RNDN);
        ex11_hp(v, rhp);
        
        mpfr_t temp;
        mpfr_init2(temp, PRECISION);
        mpfr_set_d(temp, 0, MPFR_RNDN);
        ex11_hp(nextafter(v, vend), temp);
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

