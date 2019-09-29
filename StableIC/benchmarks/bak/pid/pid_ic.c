#include <math.h>
#define TRUE 1
#define FALSE 0

double pid_ic(double m){
    int t = 0;
    double i = 0;
    while (t < 10) {
        i = (i + (0.138012 * (5.0 - m)));
        double eold = (5.0 - m);
        m = (m + (0.01 * ((((5.0 - m) * 9.4514)
                           + i) + (((5.0 - m) - eold) * 14.227))));
        t = t + 2;
    }
    return m;
}

