#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <mpfr.h>

#define PRECISION 256

double ex8(double v, double w, double r);
double ex8_ic(double v, double w, double r);

void ex8_hp(double v, double w, double r, mpfr_t x){
    mpfr_t t1, t2, t3, t4;
    mpfr_t vmf, wmf, rmf;
    
    mpfr_init2(t1, PRECISION);
    mpfr_init2(t2, PRECISION);
    mpfr_init2(t3, PRECISION);
    mpfr_init2(t4, PRECISION);
    
    mpfr_init2(vmf, PRECISION);
    mpfr_init2(wmf, PRECISION);
    mpfr_init2(rmf, PRECISION);
    
    mpfr_set_d(vmf, v, MPFR_RNDN);
    mpfr_set_d(wmf, w, MPFR_RNDN);
    mpfr_set_d(rmf, r, MPFR_RNDN);
    
    mpfr_mul(t1, rmf, rmf, MPFR_RNDN);
    mpfr_d_div(t1, 2.0f, t1, MPFR_RNDN);
    mpfr_d_sub(t1, 3.0f, t1, MPFR_RNDN);
    
    mpfr_mul_d(t2, vmf, 2.0f, MPFR_RNDN);
    mpfr_add_d(t2, t2, 1.0f, MPFR_RNDN);
    mpfr_mul_d(t2, t2, 0.125f, MPFR_RNDN);
    
    mpfr_mul(t3, wmf, wmf, MPFR_RNDN);
    mpfr_mul(t3, t3, rmf, MPFR_RNDN);
    mpfr_mul(t3, t3, rmf, MPFR_RNDN);
    mpfr_mul(t2, t2, t3, MPFR_RNDN);
    
    mpfr_d_sub(t4, 1.0f, vmf, MPFR_RNDN);
    mpfr_div(t2, t2, t4, MPFR_RNDN);
    mpfr_sub(t1, t1, t2, MPFR_RNDN);
    
    mpfr_sub_d(x, t1, 0.5f, MPFR_RNDN);
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 1;
    double vend= 10;
    double wbegin = 1;
    double wend= 10;
    double rbegin = 1;
    double rend = 10;
    
    double v = vbegin;
    double w = wbegin;
    double r = rbegin;
    
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
    
    for(int i = 0; i < 10; i ++){
        v = v + 0.9;
        for(int j = 0; j < 100; j ++){
            w = w + 0.09;
            for(int k = 0; k < 100; k ++){
                r = r + 0.09;
                double r1 = ex8(v, w, r);
                double r2 = ex8_ic(v, w, r);
                
                mpfr_set_d(rhp, 0, MPFR_RNDN);
                ex8_hp(v, w, r, rhp);
                
                mpfr_t temp;
                mpfr_init2(temp, PRECISION);
                mpfr_set_d(temp, 0, MPFR_RNDN);
                ex8_hp(v, nextafter(w, wend), r, temp);
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

