#include <stdio.h>

//float combine_test(float x, float y){
//  float r = x + 2 + 4 + y * 5 * 6;
//  return r;
//}

//double FoldFMulConst1(double X){
//    double r = (X * 0.6) * 0.72;
//    return r;
//}

//double FoldFMulConst2(double X){
//    double r = (0.6/X) * 0.72;
//    return r;
//}

//double FoldFDivConst3(double X){
//    double r = (0.6 * X) / 0.72;
//    return r;
//}

//double FoldFDivConst4(double X){
//    double r = 0.6 / (X / 0.72);
//    return r;
//}

//double MulDivideConst(double X){
//    double r = (X * 0.6 + 0.7) * 0.9;
//    return r;
//}

//double ConstAsso1(double X){
//    double r = (6.2 + X) + 0.7;
//    return r;
//}

//double logdiff1(double X, double Y){
//    double r = (0.6/X) * 0.72;
//    r = r * Y;
//    return r;
//}

//double logdiff2(double X, double Y){
//    double r = (0.6/X) * 0.72;
//    r = r - 0.9*Y;
//    return r;
//}

double demo(double x, double y){
    double v1 = (0.6 / x) * 0.5 + 2/x;
    double v2 = v1 * y;
    double v3 = v2 + y;
    return v3;
}

