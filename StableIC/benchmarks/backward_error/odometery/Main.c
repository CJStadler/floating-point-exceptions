#include <stdio.h>
#include <math.h>
#include <mpfr.h>
#include <time.h>
#include <stdlib.h>

#define PRECISION 256

double odometer(double v);
double odometer_ic(double v);
void odometer_hp(double s1, mpfr_t y){
    mpfr_t amf, bmf, cmf, smf;
    mpfr_t TMP_6, TMP_29, TMP_27, TMP_26, theta;
    
    mpfr_init2(amf, PRECISION);
    mpfr_init2(bmf, PRECISION);
    mpfr_init2(cmf, PRECISION);
    mpfr_init2(smf, PRECISION);
    
    mpfr_init2(TMP_6, PRECISION);
    mpfr_init2(TMP_29, PRECISION);
    mpfr_init2(TMP_27, PRECISION);
    mpfr_init2(TMP_26, PRECISION);
    mpfr_init2(theta, PRECISION);
    
    mpfr_set_d(smf, s1, MPFR_RNDN);
    mpfr_set_d(theta, 0, MPFR_RNDN);
    mpfr_set_d(y, 0, MPFR_RNDN);
    
    for(int i = 0; i < 100; i ++){
        mpfr_mul_d(TMP_6,   smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_6, TMP_6, 9.691813336318980,  MPFR_RNDN);
        mpfr_mul_d(TMP_6, TMP_6, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.1, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_6);
        
        mpfr_add(TMP_26, theta, TMP_6, MPFR_RNDN);
        
        mpfr_mul_d(TMP_27, smf, 12.34, MPFR_RNDN);
        mpfr_d_sub(TMP_27, 9.691813336318980, TMP_27, MPFR_RNDN);
        mpfr_mul_d(TMP_27,  TMP_27, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_27,  TMP_27, 0.1, MPFR_RNDN);
        mpfr_add(TMP_27, theta, TMP_27, MPFR_RNDN);
        mpfr_mul(TMP_27, TMP_27, TMP_26, MPFR_RNDN);
        mpfr_mul(TMP_27, TMP_27, TMP_26, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_23);
        
        
        //mpfr_printf("RAT %.128RNf\n", TMP_26);
        
        mpfr_mul(TMP_29, TMP_27, TMP_26, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_25);
        
        mpfr_div_d(amf, TMP_27, 6.0, MPFR_RNDN);
        mpfr_sub(amf, TMP_26, amf, MPFR_RNDN);
        mpfr_mul(bmf, TMP_29, TMP_26, MPFR_RNDN);
        mpfr_div_d(bmf, bmf, 120.0, MPFR_RNDN);
        mpfr_add(amf, amf, bmf, MPFR_RNDN);
        mpfr_mul_d(amf, amf, 0.5, MPFR_RNDN);
        
        mpfr_mul_d(cmf,  smf, 12.34, MPFR_RNDN);
        mpfr_add_d(cmf, cmf, 9.691813336318980, MPFR_RNDN);
        mpfr_mul(amf, amf, cmf, MPFR_RNDN);
        mpfr_add(y, amf, y, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", x);
        
        mpfr_mul_d(amf, smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(amf, amf, 9.691813336318980, MPFR_RNDN);
        mpfr_mul_d(amf, amf, -1, MPFR_RNDN);
        mpfr_mul_d(amf,  amf, 0.1, MPFR_RNDN);
        mpfr_add(theta, amf, theta, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", theta);
    }
    
    mpfr_clear(amf);
    mpfr_clear(bmf);
    mpfr_clear(cmf);
    mpfr_clear(smf);
    
    mpfr_clear(TMP_6);
    mpfr_clear(TMP_29);
    mpfr_clear(TMP_27);
    mpfr_clear(TMP_26);
    mpfr_clear(theta);
    
}

int main(){
    
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
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
    
    int k = 0;
    double vbegin = 0.1;
    double vend =   0.2;
    double v = vbegin;
    
    for(int i = 0; i < 100000; i ++){
        v =  v + 0.000001;
        //v= 0.52998999869999819;
        
        double r1 = odometer(v);
        double r2 = odometer_ic(v);
        
        mpfr_set_d(rhp, 0, MPFR_RNDN);
        odometer_hp(v, rhp);
        
        mpfr_t temp;
        mpfr_init2(temp, PRECISION);
        mpfr_set_d(temp, 0, MPFR_RNDN);
        odometer_hp(nextafter(v, vend), temp);
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


