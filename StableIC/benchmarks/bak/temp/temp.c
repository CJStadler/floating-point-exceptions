#include <stdio.h>
double odometer(){
   double sl = 0.5299899986;
   double sr = 0.785398163397, theta = 0.0,
    t = 0.0, x = 0.0, y = 0.0, inv_l = 0.1, c = 12.34;
    while (t < 100.0) {
        double delta_dl = (c * sl);
        double delta_dr = (c * sr);
        double delta_d = ((delta_dl + delta_dr) * 0.5);
        double delta_theta = ((delta_dr - delta_dl) * inv_l);
        double arg  = (theta + (delta_theta * 0.5));
        double cos  = (1.0 - ((arg * arg) * 0.5)) + ((((arg * arg)* arg)* arg) / 24.0);
        x = (x + (delta_d * cos));
        printf("Result %.17f\n", x);
        double sin  = (arg - (((arg * arg)* arg)/6.0)) + (((((arg * arg)* arg)* arg)* arg)/120.0);
        y =   (y + (delta_d * sin));
        theta = (theta + delta_theta);
        t = (t + 0.1);
    }
    return x;
}

int main(){
    odometer();
}

   
    
  


