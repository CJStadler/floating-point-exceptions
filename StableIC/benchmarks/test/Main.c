#include <stdio.h>
#include <math.h>
#include <mpfr.h>

#define PRECISION 256


float combine_test(float x, float y);
double FoldFMulConst1(double X);
double FoldFMulConst2(double X);
double FoldFDivConst3(double X);
double FoldFDivConst4(double X);
double MulDivideConst(double X);
double ConstAsso1(double X);
double logdiff1(double X, double Y);
double logdiff2(double X, double Y);
double demo(double x, double y);

float combine_test_ic(float x, float y);
double FoldFMulConst1_ic(double X);
double FoldFMulConst2_ic(double X);
double FoldFDivConst3_ic(double X);
double FoldFDivConst4_ic(double X);
double MulDivideConst_ic(double X);
double ConstAsso1_ic(double X);
double logdiff1_ic(double X, double Y);
double logdiff2_ic(double X, double Y);

double demo_ic(double x, double y);
double demo(double x, double y);

void demo_hp(double x, double y, mpfr_t vmf){
    mpfr_t tmp1;
    mpfr_t tmp2;
    mpfr_init2(tmp1, PRECISION);
    mpfr_init2(tmp2, PRECISION);
    
    
    mpfr_set_d(tmp1, 0.6, MPFR_RNDN);
    mpfr_div_d(tmp1, tmp1, x, MPFR_RNDN);
    mpfr_mul_d(tmp1, tmp1, 0.5, MPFR_RNDN);
    
    mpfr_set_d(tmp2, 2, MPFR_RNDN);
    mpfr_div_d(tmp2, tmp2, x, MPFR_RNDN);
    mpfr_add(tmp1, tmp1, tmp2, MPFR_RNDN);
    
    mpfr_mul_d(tmp1, tmp1, y, MPFR_RNDN);
    mpfr_add_d(vmf, tmp1, y, MPFR_RNDN);
    
    mpfr_clear(tmp1);
    mpfr_clear(tmp2);
    
}

int main(){
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double vbegin = -2.29;
    double vend = -2.28;
    double wbegin = 100;
    double wend = 101;
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
    
    for(int i = 0; i < 10000; i ++){
        v =  v + 0.00001;
        for(int j = 0; j < 100; j ++){
            w =  w + 0.001;
            double r1 = demo(v, w);
            double r2 = demo_ic(v, w);
            
            mpfr_set_d(rhp, 0, MPFR_RNDN);
            demo_hp(v,w, rhp);
            
            mpfr_t temp;
            mpfr_init2(temp, PRECISION);
            mpfr_set_d(temp, 0, MPFR_RNDN);
            demo_hp(nextafter(v, vend), nextafter(w, wend), temp);
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

