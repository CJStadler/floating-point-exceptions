#include <stdlib.h>
#include <stdio.h>

#include "../exception_counters.h"

// Interfaces for P and P'
double p_unopt(double input);
double p_opt(double input);

int main(int argc, char** argv) {
  if (argc < 2) {
    puts("Input required");
    exit(1);
  }
  double input = atof(argv[1]);
  printf("input = %f\n", input);
  puts("Running unopt");
  p_unopt(input);
  reset_counts();
  puts("");
  puts("Running opt");
  p_opt(input);
}
