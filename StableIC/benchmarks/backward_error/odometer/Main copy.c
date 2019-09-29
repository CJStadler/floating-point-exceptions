#include <stdio.h>
#include <math.h>
#include <mpfr.h>
#include <stdlib.h>
#include <random>

#define PRECISION 256


double odometer(double v);
double odometer_ic(double v);
void odometer_hp(mpfr_t smf, mpfr_t x){
    mpfr_t amf, bmf, cmf;
    mpfr_t TMP_6, TMP_23, TMP_25, TMP_26, theta;
    
    mpfr_init2(amf, PRECISION);
    mpfr_init2(bmf, PRECISION);
    mpfr_init2(cmf, PRECISION);
    
    mpfr_init2(TMP_6, PRECISION);
    mpfr_init2(TMP_23, PRECISION);
    mpfr_init2(TMP_25, PRECISION);
    mpfr_init2(TMP_26, PRECISION);
    mpfr_init2(theta, PRECISION);
    
    mpfr_set_d(theta, 0, MPFR_RNDN);
    mpfr_set_d(x, 0, MPFR_RNDN);
    
    for(int i = 0; i < 100; i ++){
        mpfr_mul_d(TMP_6,   smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_6, TMP_6, 9.691813336318980,  MPFR_RNDN);
        mpfr_mul_d(TMP_6, TMP_6, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_6,  TMP_6, 0.1, MPFR_RNDN);
        //        //mpfr_printf("RAT %.128RNf\n", TMP_6);
        //
        mpfr_mul_d(TMP_23, smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_23, TMP_23, 9.691813336318980, MPFR_RNDN);
        mpfr_mul_d(TMP_23, TMP_23, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_23,  TMP_23, 0.5, MPFR_RNDN);
        mpfr_mul_d(TMP_23,  TMP_23, 0.1, MPFR_RNDN);
        mpfr_add(TMP_23, theta, TMP_23, MPFR_RNDN);
        mpfr_mul(TMP_23, TMP_23, TMP_23, MPFR_RNDN);
        //        //mpfr_printf("RAT %.128RNf\n", TMP_23);
        //
        mpfr_add(TMP_26, theta, TMP_6, MPFR_RNDN);
        ////        mpfr_printf("RAT %.128RNf\n", TMP_26);
        //
        mpfr_mul_d(TMP_25,   smf, 12.34, MPFR_RNDN);
        mpfr_sub_d(TMP_25,  TMP_25, 9.691813336318980, MPFR_RNDN);
        mpfr_mul_d(TMP_25, TMP_25, -1, MPFR_RNDN);
        mpfr_mul_d(TMP_25,  TMP_25, 0.1, MPFR_RNDN);
        mpfr_mul_d(TMP_25,  TMP_25, 0.5, MPFR_RNDN);
        mpfr_add(TMP_25, theta, TMP_25, MPFR_RNDN);
        mpfr_mul(TMP_25, TMP_25, TMP_26, MPFR_RNDN);
        mpfr_mul(TMP_25, TMP_25, TMP_26, MPFR_RNDN);
        //                //mpfr_printf("RAT %.128RNf\n", TMP_25);
        //
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
        mpfr_mul_d(amf, amf, 0.1, MPFR_RNDN);
        mpfr_add(theta, amf, theta, MPFR_RNDN);
        //mpfr_printf("RAT %.128RNf\n", theta);
        
    }
    
    mpfr_clear(amf);
    mpfr_clear(bmf);
    mpfr_clear(cmf);
    
    mpfr_clear(TMP_6);
    mpfr_clear(TMP_23);
    mpfr_clear(TMP_25);
    mpfr_clear(TMP_26);
    mpfr_clear(theta);
    
}



int main(){
    
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    mpfr_t vhp, rhp, redmax, redmax_re1, redmax_re2, re1max, re2max, re, re1, re2, lemax;
    mpfr_init2(vhp, PRECISION);
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
    double vend =   0.1001;
    double v = vbegin;
    
    int bedmax = 0;

   for(int i = 0; i < 10000; i ++){
        v =  v + 0.00000001;
        //v= 0.52998999869999819;

        double r1 = odometer(v);
        double r2 = odometer_ic(v);

        mpfr_set_d(rhp, 0, MPFR_RNDN);
        mpfr_set_d(vhp, v, MPFR_RNDN);
        odometer_hp(vhp, rhp);

        mpfr_sub_d(re1, rhp, r1, MPFR_RNDN);
        mpfr_abs(re1, re1, MPFR_RNDN);

        mpfr_sub_d(re2, rhp, r2, MPFR_RNDN);
        mpfr_abs(re2, re2, MPFR_RNDN);
       
       ulpd = nextafter(v, vend) - v;
       
       int be1 = 0, be2 = 0;
       
       int j = 1;
       while(true){
           mpfr_t temp, temp_vhp;
           mpfr_init2(temp, PRECISION);
           mpfr_set_d(temp, 0, MPFR_RNDN);
           
           mpfr_init2(temp_vhp, PRECISION);
           mpfr_set_d(temp_vhp, ulpd, MPFR_RNDN);
           mpfr_mul_d(temp_vhp, temp_vhp, j, MPFR_RNDN);
           mpfr_add_d(temp_vhp, temp_vhp, v, MPFR_RNDN);
           odometer_hp(temp_vhp, temp);
           mpfr_sub(temp, temp, rhp, MPFR_RNDN);
           mpfr_abs(temp, temp, MPFR_RNDN);
           if(mpfr_cmp(temp, re1) > 0 && be1 == 0){
               be1 = j;
           }
           if(mpfr_cmp(temp, re2) > 0 && be2 == 0){
               be2 = j;
           }
      
           if(be1 != 0 && be2 != 0){
               break;
           }
           mpfr_clear(temp);
           mpfr_clear(temp_vhp);
           j ++;
       }
       
       if(abs(be1 - be2) > bedmax){
           bedmax = abs(be1 - be2);
           printf("%d %d\n", be1, be2);
           printf("%.17f\n", v);
       }

//        mpfr_sub(re, re1, re2, MPFR_RNDN);
//        mpfr_abs(re, re, MPFR_RNDN);
//        mpfr_div_d(re, re, ulpd, MPFR_RNDN);
//        mpfr_div_d(re1, re1, ulpd, MPFR_RNDN);
//        mpfr_div_d(re2, re2, ulpd, MPFR_RNDN);
//        mpfr_div_d(temp, temp, ulpd, MPFR_RNDN);
//
//        if(mpfr_cmp(re, redmax) > 0){
//            maxd = fabs(r1 - r2);
//
//            mpfr_set(redmax, re, MPFR_RNDN);
//            mpfr_set(redmax_re1, re1, MPFR_RNDN);
//            mpfr_set(redmax_re2, re2, MPFR_RNDN);
//
//            result1 = r1;
//            result2 = r2;
//            max_input = v;
//        }
//
//        if(mpfr_cmp(re1, re1max) > 0){
//            mpfr_set(re1max, re1, MPFR_RNDN);
//        }
//
//        if(mpfr_cmp(re2, re2max) > 0){
//            mpfr_set(re2max, re2, MPFR_RNDN);
//        }
//
//        if(mpfr_cmp(re1, re2) > 0){
//            mpfr_add(temp, temp, re2, MPFR_RNDN);
//            mpfr_sub(re, re, temp, MPFR_RNDN);
//        }else{
//            mpfr_add(temp, temp, re1, MPFR_RNDN);
//            mpfr_sub(re, re, temp, MPFR_RNDN);
//        }
//
//        if(mpfr_cmp(re, lemax) > 0){
//            mpfr_set(lemax, re, MPFR_RNDN);
//        }
    }

    printf("Max Backward Error Difference: %d\n", bedmax);
//    printf("Max Input %.17f\n", max_input);
//    printf("Result %.17f\n", result1);
//    printf("Result %.17f\n", result2);
//    printf("ULP %.17f\n", ulpd);
//    mpfr_printf("LEMAX %.128RNf\n", lemax);
//    mpfr_printf("REDMAX %.128RNf\n", redmax);
//    mpfr_printf("REDMAX_RE1 %.128RNf\n", redmax_re1);
//    mpfr_printf("REDMAX_RE2 %.128RNf\n", redmax_re2);
//    mpfr_printf("RE1MAX %.128RNf\n", re1max);
//    mpfr_printf("RE2MAX %.128RNf\n", re2max);

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


