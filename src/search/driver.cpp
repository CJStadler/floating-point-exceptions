#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include <fenv.h>
#include <random>
#include <vector>

#include "../fp_exception.hpp"

extern ExceptionTrace last_trace;

// Interfaces for P and P'
double p_unopt(std::vector<double>* args);
double p_opt(std::vector<double>* args);

int main(int argc, char* argv[]) {
  double _r1 = p_unopt(input);
  ExceptionTrace trace_opt = last_trace;
  double _r2 = p_opt(input);
  ExceptionTrace trace_unopt = last_trace;
}
