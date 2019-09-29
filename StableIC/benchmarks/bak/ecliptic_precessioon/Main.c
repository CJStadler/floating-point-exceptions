#include <stdio.h>
#include <math.h>
#include <mpfr.h>

#define PRECISION 256

double ex6(double v);
double ex6_ic(double v);

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
    
    double vbegin = 915.7;
    double vend= 916;
    double wbegin = 1.4;
    double wend= 1.9;
    double rbegin = 3.8;
    double rend = 7.8;
    
    double v = vbegin;
    double w = wbegin;
    double r = rbegin;
    
    mpfr_t rhp, remax, re1max, re2max, re, re1, re2;
    mpfr_init2(rhp, PRECISION);
    mpfr_init2(remax, PRECISION);
    mpfr_init2(re1max, PRECISION);
    mpfr_init2(re2max, PRECISION);
    mpfr_init2(re, PRECISION);
    mpfr_init2(re1, PRECISION);
    mpfr_init2(re2, PRECISION);
    
    mpfr_set_d(remax, 0, MPFR_RNDN);
    
    for(int i = 0; i < 1000000; i ++){
        v= nextafter(v, vend);
                double r1 = ex6(v);
                double r2 = ex6_ic(v);
                
                mpfr_set_d(rhp, 0, MPFR_RNDN);
                ex6_hp(v, 2, 2, rhp);
                
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
                        ulpd = nextafter(r2, r1) - r2;
                    }else{
                        ulpd = nextafter(r1, r2) - r1;
                    }
                    result1 = r1;
                    result2 = r2;
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
