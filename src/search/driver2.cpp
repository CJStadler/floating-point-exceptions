#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include <fenv.h>
#include <random>

#include "../exception_counters.h"

// Interfaces for P and P'
double p_unopt(double input, double input2);
double p_opt(double input, double input2);

const double SEED = 59.3;
const int ITERATIONS = 100000000;
const double INPUT_MAX = 1.0e-307;
const double INPUT_MIN = -INPUT_MAX;

int check_exceptions() {
  // Return the total number of exceptions
  int total = overflows
            + underflows
            + divbyzeros
            + invalids;
  reset_counts();
  return total;
}

int main() {
  std::default_random_engine generator(SEED);
  std::uniform_real_distribution<double> distribution(INPUT_MIN, INPUT_MAX);

  double input;
  double input2;

  int only_unopt = 0;
  int only_opt = 0;
  int both = 0;
  int neither = 0;

  printf("Running %i iterations\n", ITERATIONS);

  for (int i = 0; i < ITERATIONS; i++) {
    input = distribution(generator);
    input2 = distribution(generator);
    reset_counts();
    feclearexcept(FE_ALL_EXCEPT);
    double _r1 = p_unopt(input, input2);
    int exceptions_unopt = check_exceptions();
    double _r2 = p_opt(input, input2);
    int exceptions_opt = check_exceptions();

    if (exceptions_unopt > 0 || exceptions_opt > 0) {
      fprintf(stderr, "input: (%.17e, %.17e) unopt: %i opt: %i\n",
          input, input2, exceptions_unopt, exceptions_opt);
    }

    // Increment the appropriate counter.
    if (exceptions_unopt > 0) {
      if (exceptions_opt > 0) {
        both++;
      } else {
        only_unopt++;
      }
    } else if (exceptions_opt > 0) {
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
