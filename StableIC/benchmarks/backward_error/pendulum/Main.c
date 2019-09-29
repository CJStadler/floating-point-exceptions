#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <mpfr.h>

#define PRECISION 256

double ex5(double v, double w);
double ex5_ic(double v, double w);

void ex5_hp(double t, double w, mpfr_t vmf){
    mpfr_t tmp1;

    mpfr_init2(tmp1, PRECISION);
    
    mpfr_set_d(tmp1, t, MPFR_RNDN);
    mpfr_sin(tmp1, tmp1, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, -9.80665, MPFR_RNDN);
    mpfr_div_d(tmp1, tmp1, 2.0, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, 0.01, MPFR_RNDN);
    mpfr_div_d(tmp1, tmp1, 2, MPFR_RNDN);
    mpfr_add_d(tmp1, tmp1, w, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, 0.01, MPFR_RNDN);
    mpfr_add_d(vmf, tmp1, t, MPFR_RNDN);

    mpfr_clear(tmp1);
    
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 1;
    double vend = 10;
    double wbegin = 1;
    double wend = 10;
    double v = vbegin;
    double w = wbegin;
    
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

    
    for(int i = 0; i < 1000; i ++){
        v =  v + 0.009;
        for(int j = 0; j < 100; j ++){
            w =  w + 0.09;
            double r1 = ex5(v, w);
            double r2 = ex5_ic(v, w);
            
            mpfr_set_d(rhp, 0, MPFR_RNDN);
            ex5_hp(v,w, rhp);
            
            mpfr_t temp;
            mpfr_init2(temp, PRECISION);
            mpfr_set_d(temp, 0, MPFR_RNDN);
            ex5_hp(nextafter(v, vend), nextafter(w, wend), temp);
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

