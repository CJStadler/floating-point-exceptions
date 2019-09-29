#include <stdio.h>
#include <math.h>

#include "Random.h"

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
    
    mfpr_mul(t1, rmf, rmf, MPFR_RNDN);
    mpfr_d_div(t1, 2.0f, t1, MPFR_RNDN);
    mpfr_add_d(t1, t1, 3.0f, MPFR_RNDN);
    
    mpfr_mul_d(t2, v, 2.001f, MPFR_RNDN);
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
  Random R = new_Random(110110, 1.99, 2.0);
  double maxd = 0.0;
  double ulpd = 0.0;
      double result = 0.0;
  
  for(int i = 0; i < 10000; i ++){
    double v = Random_nextDouble(R);
    double w = Random_nextDouble(R);
    double r = Random_nextDouble(R);
    double r1 = ex6(v, w, r);
    double r2 = ex6_ic(v, w, r);
    if(fabs(r1 - r2) > maxd){
      maxd = fabs(r1 - r2);
        ulpd =  r1 * (nextafter(1.0, 2.0) - 1.0);
        result = r1;

    }
  }
  printf("Result %.17f\n", result);
  printf("Op and Nonop DIFF %.17f\n", maxd);
  printf("ULP %.17f\n", ulpd);
}
