#include <stdio.h>
#include <math.h>

#define GSL_DBL_EPSILON 2.2204460492503131e-16

int gsl_sf_bessel_Knu_scaled_asympx_e(const double nu, const double x) {
  double mu = 4.0*nu*nu;
  double mum1 = mu-1.0;
  double mum9 = mu-9.0;
  double pre = sqrt(M_PI/(2.0*x));
  double r = nu/x;
  double result1 = pre * (1.0 + mum1/(8.0*x) + mum1*mum9/(128.0*x*x));
  double result2 = 2.0 * GSL_DBL_EPSILON
    * fabs(result1)
    + pre * fabs(0.1*r*r*r);
  /* The below is just to prevent optimizing away result1 and and result2 */
  if (result1 > 0 && result2 > 0) {
    return 1;
  } else {
    return 0;
  }
}
