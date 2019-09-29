#include <stdio.h>
#include <math.h>
#include <mpfr.h>
#include <time.h>
#include <stdlib.h>

#include "Random.h"

#define PRECISION 256

double pid(double v);
double pid_ic(double v);
void odometer_hp(double s1, mpfr_t x){
    mpfr_t amf, bmf, cmf, smf;
    mpfr_t TMP_6, TMP_23, TMP_25, TMP_26, theta;
    
    mpfr_init2(amf, PRECISION);
    mpfr_init2(bmf, PRECISION);
    mpfr_init2(cmf, PRECISION);
    mpfr_init2(smf, PRECISION);
    
    mpfr_init2(TMP_6, PRECISION);
    mpfr_init2(TMP_23, PRECISION);
    mpfr_init2(TMP_25, PRECISION);
    mpfr_init2(TMP_26, PRECISION);
    mpfr_init2(theta, PRECISION);
    
    mpfr_set_d(smf, s1, MPFR_RNDN);
    mpfr_set_d(theta, 0, MPFR_RNDN);
    mpfr_set_d(x, 0, MPFR_RNDN);
    
    for(int i = 0; i < 100; i ++){
        mpfr_mul_d(TMP_6,   smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_6, TMP_6, 9.691813336318980,  MPFR_RNDN);
        mpfr_mul_d(TMP_6, TMP_6, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.1, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_6);
        
        mpfr_mul_d(TMP_23, smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_23, TMP_23, 9.691813336318980, MPFR_RNDN);
        mpfr_mul_d(TMP_23, TMP_23, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_23,  TMP_23, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_23,  TMP_23, 0.1, MPFR_RNDN);
        mpfr_add(TMP_23, theta, TMP_23, MPFR_RNDN);
        mpfr_mul(TMP_23, TMP_23, TMP_23, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_23);
        
        mpfr_add(TMP_26, theta, TMP_6, MPFR_RNDN);
//        mpfr_printf("RAT %.128RNf\n", TMP_26);
        
        mpfr_mul_d(TMP_25,   smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_25,  TMP_25, 9.691813336318980, MPFR_RNDN);
        mpfr_mul_d(TMP_25, TMP_25, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_25,  TMP_25, 0.1, MPFR_RNDN);
        mpfr_mul_d(TMP_25,  TMP_25, 0.5, MPFR_RNDN);
        mpfr_add(TMP_25, theta, TMP_25, MPFR_RNDN);
        mpfr_mul(TMP_25, TMP_25, TMP_26, MPFR_RNDN);
        mpfr_mul(TMP_25, TMP_25, TMP_26, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", TMP_25);
        
        mpfr_mul_d(amf, TMP_23, 0.5, MPFR_RNDN);
        mpfr_sub_d(amf, amf, 1.0, MPFR_RNDN);
        mpfr_mul_d(amf, amf, -1, MPFR_RNDN);
        mpfr_mul(bmf, TMP_25, TMP_26, MPFR_RNDN);
        mpfr_div_d(bmf, bmf, 24.0, MPFR_RNDN);
        mpfr_add(bmf, amf, bmf, MPFR_RNDN);
        
        mpfr_mul_d(cmf,  smf, 12.34, MPFR_RNDN);
        mpfr_add_d(cmf, cmf, 9.691813336318980, MPFR_RNDN);
        mpfr_mul(cmf, bmf, cmf, MPFR_RNDN);
        mpfr_mul_d(cmf, cmf, 0.5, MPFR_RNDN);
        mpfr_add(x, cmf, x, MPFR_RNDN);
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
    mpfr_clear(TMP_23);
    mpfr_clear(TMP_25);
    mpfr_clear(TMP_26);
    mpfr_clear(theta);
    
}

int main(){
    Random R = new_Random(140110, 0.529910, 0.529911);
    
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    mpfr_t r;
    mpfr_init2(r, PRECISION);
    
    
    mpfr_t r1mf, r2mf, re1, re2, re1_abs, re2_abs, re1_max, re2_max, re_time;
    mpfr_init2(r1mf, PRECISION);
    mpfr_init2(r2mf, PRECISION);
    mpfr_init2(re1, PRECISION);
    mpfr_init2(re2, PRECISION);
    mpfr_init2(re1_abs, PRECISION);
    mpfr_init2(re2_abs, PRECISION);
    mpfr_init2(re1_max, PRECISION);
    mpfr_init2(re2_max, PRECISION);
    mpfr_init2(re_time, PRECISION);
    
    for(int j = 100000; j < 100001; j ++){
        mpfr_set_d(re2_max, 0, MPFR_RNDN);
        mpfr_set_d(re1_max, 0, MPFR_RNDN);
        mpfr_set_d(re_time, 0, MPFR_RNDN);
        
        int k = 0;
        double begin = 0.5;
        double end =   0.6;
        double v = begin;
        srand(time(NULL));
        
        while(v < end && k < 200000000){
            //double v = Random_nextDouble(R);
            v =  (nextafter(v, end));
            double r1 = pid(v);
            double r2 = pid_ic(v);
            if(fabs(r1 - r2) > maxd){
                maxd = fabs(r1 - r2);
                max_input = v;
                result1 = r1;
                result2 = r2;
                if(r1 > r2){
                    ulpd = nextafter(r2, r1) - r2;
                }else{
                    ulpd = nextafter(r1, r2) - r1;
                }
            }
            
            //mpfr_set_d(r, 0, MPFR_RNDN);
            //odometer_hp(v, r);
          
            k ++;
        }
        printf("%d\n", k);
        printf("Input %.17f\n", max_input);
        printf("Result %.17f\n", result1);
        printf("Result %.17f\n", result2);
        printf("ABS %.17f\n", maxd);
        printf("ULP %.17f\n", ulpd);
        mpfr_printf("RAT %.128RNf\n", re1_max);
        mpfr_printf("RAT %.128RNf\n", re1);
        mpfr_printf("RAT %.128RNf\n", re2);
    }
    mpfr_clear(r1mf);
    mpfr_clear(r2mf);
    mpfr_clear(re1);
    mpfr_clear(re2);
    mpfr_clear(r);
    
}
