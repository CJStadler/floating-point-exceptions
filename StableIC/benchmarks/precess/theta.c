#define PI 3.1415926535897932384626433832795028841971693993751058209749445923
double caln(double t_centuries){
    //return (3.07496 + .00186 * t_centuries / 2.) * (PI / 180.) / 240.;
   return (1.33621 - .00057 * t_centuries / 2.) * (PI / 180.) / 240.;
}

