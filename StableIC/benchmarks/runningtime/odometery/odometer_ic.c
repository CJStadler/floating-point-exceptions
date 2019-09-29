#include <math.h>

double odometer_ic(double sl){
    double theta = 0.0, y = 0.0, x = 0.0;
    for (int i = 0; i < 100; i++) {
        double TMP_6  = (0.1 * (0.5 * (9.691813336318980 - (12.34 * sl))));
        double TMP_23 = ((theta + (((9.691813336318980 - (sl * 12.34)) * 0.1) * 0.5))
                         * (theta + (((9.691813336318980 - (sl * 12.34)) * 0.1) * 0.5)));
        double TMP_25 = ((theta + TMP_6) * (theta + TMP_6)) * (theta + (((9.691813336318980 - (sl * 12.34)) * 0.1) * 0.5));
        double TMP_26 = (theta + TMP_6);
        x = ((0.5 * (((1.0 - (TMP_23 * 0.5)) + ((TMP_25 * TMP_26) / 24.0)) * ((12.34 * sl) + 9.691813336318980))) + x);
        double TMP_27 = ((TMP_26 * TMP_26) * (theta + (((9.691813336318980 - (sl * 12.34)) * 0.1) * 0.5)));
        double TMP_29 = (((TMP_26 * TMP_26) * TMP_26) * (theta + (((9.691813336318980 - (sl * 12.34))*0.1)*0.5)));
        y = (((9.691813336318980 + (12.34 * sl)) * (((TMP_26 - (TMP_27 /6.0)) + ((TMP_29 * TMP_26) / 120.0)) * 0.5)) + y);
        theta = (theta + (0.1 * (9.691813336318980 - (12.34 * sl))));
       // theta = calTheta(theta, sl);
//        theta = (theta + 0.9691813336318980 - (1.234 * sl));
    }
    return y;
}

