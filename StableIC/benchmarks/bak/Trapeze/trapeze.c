#include <stdio.h>

double runge_kutta(double sl){
    u = [1.11, 2.22]; xa = 0.25; r = 0.0;
    while (xa < 5000.0) do {
        TMP_1 = (0.7 * (xa + 199.99));
        TMP_2 = (xa + 199.99);
        TMP_9 = ((((0.7 * xa) * xa) * xa) - ((0.6 * xa) * xa)) + (0.9 * xa);
        TMP_11= (((199.99 + xa) * (TMP_2 * TMP_1)) - ((199.99 + xa) * (TMP_2 * 0.6)))
        + (0.9 * TMP_2);
        r = (r + ((((u / (TMP_11 - 0.2)) + (u / (TMP_9 - 0.2))) * 0.5) * 199.99));
        xa = (xa + 199.99);
    }
}
