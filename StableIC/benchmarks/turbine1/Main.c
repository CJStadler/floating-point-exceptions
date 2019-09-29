#include <stdio.h>
#include <math.h>
#include <mpfr.h>

#define PRECISION 256

double ex6(double v, double w, double r);
double ex6_ic(double v, double w, double r);

void ex6_hp(double v, double w, double r, mpfr_t x){
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
    mpfr_add_d(t1, t1, 3.0f, MPFR_RNDN);
    
    mpfr_mul_d(t2, vmf, 2.0f, MPFR_RNDN);
    mpfr_d_sub(t2, 3.0f, t2, MPFR_RNDN);
    mpfr_mul_d(t2, t2, 0.125f, MPFR_RNDN);
    
    mpfr_mul(t3, wmf, wmf, MPFR_RNDN);
    mpfr_mul(t3, t3, rmf, MPFR_RNDN);
    mpfr_mul(t3, t3, rmf, MPFR_RNDN);
    mpfr_mul(t2, t2, t3, MPFR_RNDN);
    
    mpfr_d_sub(t4, 1.0f, vmf, MPFR_RNDN);
    mpfr_div(t2, t2, t4, MPFR_RNDN);
    mpfr_sub(t1, t1, t2, MPFR_RNDN);
    
    mpfr_sub_d(x, t1, 4.5f, MPFR_RNDN);
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = -4;
    double vend= -1;
    double wbegin = 1.5;
    double wend= 2;
    double rbegin = 4;
    double rend = 8;
    
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
    
    
    for(int i = 0; i < 100; i ++){
        v = v + 0.03;
        for(int j = 0; j < 100; j ++){
            w = w + 0.005;
            for(int k = 0; k < 100; k ++){
                r = r + 0.04;
                double r1 = ex6(v, w, r);
                double r2 = ex6_ic(v, w, r);
                
                mpfr_set_d(rhp, 0, MPFR_RNDN);
                ex6_hp(v, w, r, rhp);
                
                mpfr_t temp;
                mpfr_init2(temp, PRECISION);
                mpfr_set_d(temp, 0, MPFR_RNDN);
                ex6_hp(nextafter(v, vend), nextafter(w, wend), nextafter(r, rend), temp);
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
