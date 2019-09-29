#include <iostream>
#include <chrono>

using namespace std;

double odometer(double v);
double odometer_ic(double v);

int main(){
    
    double maxd = 0.0;
    double ulpd = 0.0;
    double result1 = 0.0;
    double result2 = 0.0;
    double max_input = 0.0;
    
    double begin = 0.525;
    double v = begin;
    
    auto start = chrono::steady_clock::now();
    //for(int i = 0; i < 5; i ++){
        //v =  v + dist * pow(2, 20);
        //v= 0.52998999869999819;
        double r1 = odometer(v);
    //}
    auto end = chrono::steady_clock::now();
    auto diff = end - start;
    cout << chrono::duration <double, nano> (diff).count() << " ns" << endl;
    
    start = chrono::steady_clock::now();
    //for(int i = 0; i < 5; i ++){
       double r2 = odometer_ic(v);
   // }
    end = chrono::steady_clock::now();
    diff = end - start;
    cout << chrono::duration <double, nano> (diff).count() << " ns" << endl;
}
