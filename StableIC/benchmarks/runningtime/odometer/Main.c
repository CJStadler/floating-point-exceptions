#include <iostream>
#include <chrono>
#include <math.h>

using namespace std;

double odometer_ic(double sl){
    double theta = 0.0, y = 0.0, x = 0.0;
    for (int i = 0; i < 10000; i++) {
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
    }
    return x;
}


int main(){
    double v = 0.1;
    
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    for(int i = 0; i < 100000; i ++){
       double r2 = odometer_ic(v);
    }
    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    std::cout << "Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() <<std::endl;
}
