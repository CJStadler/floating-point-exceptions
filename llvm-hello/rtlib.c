#include <stdio.h>
#include <float.h>

/* Runtime functions */

void logop(double i) {
  if (i > DBL_MAX) {
    puts("Detected Overflow");
  } else if (i < DBL_MIN) {
    puts("Detected Underflow");
  }
}
