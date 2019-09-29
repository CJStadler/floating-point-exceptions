#include <stdio.h>
#include <math.h>
#define TRUE 1
#define FALSE 0
#define J2000  2451545.
#define PI 3.1415926535897932384626433832795028841971693993751058209749445923

//float combine_test_ic(float x, float y){
//  float r = x + 2 + 4 + y * 5 * 6;
//  return r;
//}

//double FoldFMulConst1_ic(double X){
//    double r = (X * 0.6) * 0.72;
//    return r;
//}

//double FoldFMulConst2_ic(double X){
//    double r = (0.6/X) * 0.72;
//    return r;
//}

//double FoldFDivConst3_ic(double X){
//    double r = (0.6 * X) / 0.72;
//    return r;
//}

//double FoldFDivConst4_ic(double X){
//    double r = 0.6 / (X / 0.72);
//    return r;
//}

//double MulDivideConst_ic(double X){
//    double r = (X * 0.6 + 0.7) * 0.9;
//    return r;
//}

//double ConstAsso1_ic(double X){
//    double r = (6.2 + X) + 0.7;
//    return r;
//}

//double logdiff1_ic(double X, double Y){
//    double r = (0.6/X) * 0.72;
//    r = r * Y;
//    return r;
//}

//double logdiff2_ic(double X, double Y){
//    double r = (0.6/X) * 0.72;
//    r = r - 0.9*Y;
//    return r;
//}

double demo_ic(double x){
    double y = 5;
    double v1 = (0.6 / x) * 0.5 + 2/x;
    double v2 = v1 * y;
    double v3 = v2 + y;
    return v3;
}

