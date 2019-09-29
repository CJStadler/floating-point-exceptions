#define PI 3.1415926535897932384626433832795028841971693993751058209749445923
double calLongitude(double jd){
   return (200.913 + 61.2588532 * (jd - 2433282.5)) * (PI / 180.);
}

double calTMP6(double sl){
    return (0.1 * (0.5 * (9.691813336318980 - (12.34 * sl))));
}
