#include <stdlib.h>
#include <stdio.h>

#include "../exception_counters.h"

// Interfaces for P and P'
double p_unopt(double input);
double p_opt(double input);

int check_exceptions() {
  // Return the total number of exceptions
  int total = overflows
            + underflows
            + divbyzeros
            + invalids;
  reset_counts();
  return total;
}

int main(int argc, char** argv) {
  if (argc < 2) {
    puts("Input required");
    exit(1);
  }
  double input = atof(argv[1]);
  puts("Running unopt");
  p_unopt(input);
  int exceptions_unopt = check_exceptions();

  puts("");
  puts("Running opt");
  p_opt(input);
  int exceptions_opt = check_exceptions();

  fprintf(stderr, "input: %.10e unopt: %i opt: %i\n",
      input, exceptions_unopt, exceptions_opt);
}
