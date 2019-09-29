#include <math.h>
#define TRUE 1
#define FALSE 0

double runge_kutta_ic(double yn){
    int  t = 1;
    double yn_plus_1 = 0.0;
    while(t < 10) {
        double TMP_7 = (1.2 * (100.099 - yn));
        double TMP = 0.05 * TMP_7;
//        double TMP_8 = (100.099 - yn);
//        double TMP_13 = (1.2 * (100.099 - (yn + (0.05 * ((1.2* (100.099 - (yn + (0.05 * (TMP_7
//                                                                                         * TMP_8))))) * (100.099 - (yn + (0.05 * ((1.2 * TMP_8) * (100.099 - yn))))))))));
//        double TMP_14 = (100.099 - (yn + (0.05 * ((1.2 * 100.099 - (yn + (0.05 *(TMP_7 * TMP_8))))) *
//                                          (100.099 - (yn + (0.05 * ((1.2 * TMP_8)* (100.099 - yn))))))));
//        double TMP_18 = (yn + (0.05 * ((1.2 * (100.099 - (yn + (0.05 *(TMP_7 * TMP_8))))) * (100.099 - (yn + (0.05 * ((1.2 * TMP_8)
//                                                                                                                      * (100.099 -yn))))))));
//        double TMP_28 = ((1.2 * (100.099 - (yn + (0.05 * (TMP_7 * TMP_8))))) *(100.099 - (yn + (0.05
//                                                                                                * ((1.2 * TMP_8) * (100.099 - yn))))));
//
//        double TMP_38 = ((TMP_14 * TMP_13) * 0.1) + yn;
//        double TMP_40 = 0.1 * ((1.2 * TMP_14)*(100.099 - TMP_18));
//        yn_plus_1 = (yn + (0.016666667 * ((((TMP_7 * TMP_8) + (2.0 * TMP_28)) + (2.0 * (TMP_13 * TMP_14))) + ((1.2 * (100.099- TMP_38))* (100.099 - (yn + TMP_40))))));
        t = t + 1;
    }
    return yn_plus_1;
}

