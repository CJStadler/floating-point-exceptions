#define PI 3.1415926535897932384626433832795028841971693993751058209749445923


static const long big_N0_dot[9] = { -36507200, -15195000, -7224410,
    -3027000, -1005700, -51180, -229200, -3919, -41353 };
static const long big_P0[9] = { 106100, 309107, 0, 174800, 276590, 276590,
    69898, 352910, 280165 };
static const long big_P0_dot[9] = { 36554900, 12344121, 0, 3082000,
    51180, 51180, -1867088, 11710, -19586 };

double calLongitude(double jd){
   return (200.913 + 61.2588532 * (jd - 2433282.5)) * (PI / 180.);
}

double calTMP1(double t){
    return  t * (double)big_N0_dot[4] / 100000.;
}

double calTMP2(double t){
    return t * (double)big_P0_dot[4] / 100000.;
}
