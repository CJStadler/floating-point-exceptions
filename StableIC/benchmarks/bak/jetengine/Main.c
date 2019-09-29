#include <stdio.h>
#include <math.h>

#include <mpfr.h>

#define PRECISION 256

double ex5(double v, double w);
double ex5_ic(double v, double w);

void ex5_hp(double x2, double x1, mpfr_t vmf){
    mpfr_t tmp1, tmp2, tmpt, tmp42, tmpd, tmps, tmps42;
    
    mpfr_init2(tmpt, PRECISION);
    mpfr_init2(tmp1, PRECISION);
    mpfr_init2(tmp2, PRECISION);
    mpfr_init2(tmp42, PRECISION);
    mpfr_init2(tmpd, PRECISION);
    mpfr_init2(tmps, PRECISION);
    mpfr_init2(tmps42, PRECISION);
    
    mpfr_set_d(tmp1, 3.0, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_set_d(tmp2, 2.0, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x2, MPFR_RNDN);
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    mpfr_sub_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_set(tmpt, tmp1, MPFR_RNDN);
    
    mpfr_set_d(tmp1, 3.0, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_set_d(tmp2, 2.0, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x2, MPFR_RNDN);
    mpfr_sub(tmp1, tmp1, tmp2, MPFR_RNDN);
    mpfr_sub_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_set(tmp42, tmp1, MPFR_RNDN);
    
    mpfr_set_d(tmp1, x1, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_add_d(tmpd, tmp1, 1.0, MPFR_RNDN);
    
    mpfr_div(tmps, tmpt, tmpd, MPFR_RNDN);
    
    mpfr_div(tmps42, tmp42, tmpd, MPFR_RNDN);
    
    mpfr_sub_d(tmp1, tmps, 3.0, MPFR_RNDN);
    mpfr_mul(tmp1, tmp1, tmps, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, x1, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, 2.0, MPFR_RNDN);
    
    mpfr_mul_d(tmp2, tmps, 4.0, MPFR_RNDN);
    mpfr_sub_d(tmp2, tmp2, 6.0, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    mpfr_mul(tmp1, tmp1, tmpd, MPFR_RNDN);
    
    mpfr_set_d(tmp2, 3.0, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    mpfr_mul(tmp2, tmp2, tmps, MPFR_RNDN);
    
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    
    mpfr_set_d(tmp2, x1, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    mpfr_mul_d(tmp2, tmp2, x1, MPFR_RNDN);
    
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    
    mpfr_add_d(tmp1, tmp1, x1, MPFR_RNDN);
    
    mpfr_mul_d(tmp2, tmps42, 3.0, MPFR_RNDN);
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    
    mpfr_add_d(vmf, tmp1, x1, MPFR_RNDN);
    
    mpfr_clear(tmp1);
    mpfr_clear(tmp2);
    mpfr_clear(tmpt);
    mpfr_clear(tmp42);
    mpfr_clear(tmpd);
    mpfr_clear(tmps);
    mpfr_clear(tmps42);
    
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = 1.52;
    double vend = 1.53;
    double wbegin = 0.52;
    double wend = 0.53;
    double v = vbegin;
    double w = wbegin;
    
    mpfr_t rhp, remax, re1max, re2max, re, re1, re2;
    mpfr_init2(rhp, PRECISION);
    mpfr_init2(remax, PRECISION);
    mpfr_init2(re1max, PRECISION);
    mpfr_init2(re2max, PRECISION);
    mpfr_init2(re, PRECISION);
    mpfr_init2(re1, PRECISION);
    mpfr_init2(re2, PRECISION);
    
    mpfr_set_d(remax, 0, MPFR_RNDN);
    
    for(int i = 0; i < 10000; i ++){
        v = nextafterf(v, vend);
        for(int j = 0; j < 10000; j ++){
            w = nextafterf(w, wend);
            double r1 = ex5(v, w);
            double r2 = ex5_ic(v, w);
            
            mpfr_set_d(rhp, 0, MPFR_RNDN);
            ex5_hp(v,w, rhp);
            
            mpfr_sub_d(re1, rhp, r1, MPFR_RNDN);
            mpfr_abs(re1, re1, MPFR_RNDN);
            
            mpfr_sub_d(re2, rhp, r2, MPFR_RNDN);
            mpfr_abs(re2, re2, MPFR_RNDN);
            
            mpfr_sub(re, re1, re2, MPFR_RNDN);
            mpfr_abs(re, re, MPFR_RNDN);
            
            if(mpfr_cmp(re, remax) > 0){
                mpfr_set(remax, re, MPFR_RNDN);
                mpfr_set(re1max, re1, MPFR_RNDN);
                mpfr_set(re2max, re2, MPFR_RNDN);
                
                if(r1 > r2){
                    ulpd = nextafterf(r2, r1) - r2;
                }else{
                    ulpd = nextafterf(r1, r2) - r1;
                }
                result1 = r1;
                result2 = r2;
            }
        }
    }
    printf("ULP %.17f\n", ulpd);
    printf("Result %.17f\n", result1);
    printf("Result %.17f\n", result2);
    mpfr_printf("RAT %.128RNf\n", remax);
    mpfr_printf("RAT %.128RNf\n", re1max);
    mpfr_printf("RAT %.128RNf\n", re2max);
    
    mpfr_clear(rhp);
    mpfr_clear(remax);
    mpfr_clear(re1max);
    mpfr_clear(re2max);
    mpfr_clear(re);
    mpfr_clear(re1);
    mpfr_clear(re2);
}
