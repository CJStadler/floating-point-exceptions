#include <iostream>
#include <chrono>
#include <math.h>

double odometer(double v);
double odometer_ic(double v);

int main(){
    double v = 0.1;
    
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    for(int i = 0; i < 100000; i ++){
        double r2 = odometer(v);
    }
    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    std::cout << "Unoptimized Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() <<std::endl;
    
//    begin = std::chrono::steady_clock::now();
//    for(int i = 0; i < 100000; i ++){
//        double r2 = odometer(v);
//    }
//    end= std::chrono::steady_clock::now();
//    std::cout << "Optimized Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() <<std::endl;
    
}

