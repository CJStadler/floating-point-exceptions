#include <stdio.h>
#include <stdlib.h>
#include <random>

#include "../exception_counters.h"

// Interfaces for P and P'
double p_unopt(double input);
double p_opt(double input);

const double SEED = 31.8;
const int ITERATIONS = 1000;

int check_exceptions() {
  // Return the value of the "overflows" global, and reset it.
  double count = overflows;
  overflows = 0;
  return count;
}

int main() {
  std::default_random_engine generator(SEED);
  std::uniform_real_distribution<double> distribution(-1.0, 1.0);

  double input;

  int only_unopt = 0;
  int only_opt = 0;
  int both = 0;
  int neither = 0;

  printf("Running %i iterations\n", ITERATIONS);

  for (int i = 0; i < ITERATIONS; i++) {
    input = distribution(generator);
    double _r1 = p_unopt(input);
    int overflows_unopt = check_exceptions();
    double _r2 = p_opt(input);
    int overflows_opt = check_exceptions();

    // printf("input: %.10e unopt: %i opt: %i\n", input, overflows_unopt, overflows_opt);

    // Increment the appropriate counter.
    if (overflows_unopt > 0) {
      if (overflows_opt > 0) {
        both++;
      } else {
        only_unopt++;
      }
    } else if (overflows_opt > 0) {
      only_opt++;
    } else {
      neither++;
    }
  }

  printf("%i had no exceptions\n", neither);
  printf("%i had exceptions in both\n", both);
  printf("%i had exceptions only for opt\n", only_opt);
  printf("%i had exceptions only for unopt\n", only_unopt);
}
