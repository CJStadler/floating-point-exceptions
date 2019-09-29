#include <iostream>
#include <chrono>
#include <math.h>

double ex6(double jd);
double ex6_ic(double jd);

int main(){
    double v = 100;
    
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    for(int i = 0; i < 1000000; i ++){
        double r2 = ex6(v);
    }
    std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();
    std::cout << "Unoptimized Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() <<std::endl;
    
    begin = std::chrono::steady_clock::now();
    for(int i = 0; i < 1000000; i ++){
        double r2 = ex6_ic(v);
    }
    end= std::chrono::steady_clock::now();
    std::cout << "Optimized Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() <<std::endl;
    
}

