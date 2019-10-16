#include <stdlib.h>
#include <stdio.h>
#include <float.h>
#include <fenv.h>

/*
 * Test the unoptimized and optimized versions of a program with two inputs.
 */

// Interfaces for P and P'
double p_unopt(double input, double input2);
double p_opt(double input, double input2);

void check_exceptions() {
  int raised =
    fetestexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_DIVBYZERO | FE_INVALID);

  if (raised & FE_OVERFLOW) {
    printf("Overflow\n");
  }

  if (raised & FE_UNDERFLOW) {
    printf("Underflow\n");
  }

  if (raised & FE_DIVBYZERO) {
    printf("DivByZero\n");
  }

  if (raised & FE_INVALID) {
    printf("Invalid\n");
  }
}

int main(int argc, char** argv) {
  if (argc < 2) {
    puts("Input required");
    exit(1);
  }
  double input = atof(argv[1]);
  double input2 = atof(argv[2]);
  puts("Running unopt");
  feclearexcept(FE_ALL_EXCEPT);
  double r1 = p_unopt(input, input2);
  check_exceptions();
  printf("unopt=%.10e\n", r1);

  puts("");
  puts("Running opt");
  feclearexcept(FE_ALL_EXCEPT);
  double r2 = p_opt(input, input2);
  check_exceptions();
  printf("opt=%.10e\n", r2);

  //fprintf(stderr, "input: (%.10e, %.10e) unopt: %i opt: %i\n",
  //    input, input2, exceptions_unopt, exceptions_opt);
}
