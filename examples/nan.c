#include <stdio.h>

int main() {
    double x = -0.0;
    double y = 0.0;
    double nnan = x / y;
    int result = nnan == 0.0;
    printf("%d\n", result);
}
