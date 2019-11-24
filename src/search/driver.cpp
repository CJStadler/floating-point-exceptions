#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include <fenv.h>
#include <random>
#include <vector>
#include <sstream>
#include <string>
#include <fstream>

#include "../report_exceptions_pass/fp_exception.hpp"

// After P/P' is executed the trace will be left in this var.
extern ExceptionTrace ex_trace;

typedef std::vector<double> input_list;

// Interfaces for P and P'
double p_unopt(input_list inputs);
double p_opt(input_list inputs);

input_list parse_inputs(std::string input_str) {
  input_list inputs;

  double input;
  std::istringstream stream(input_str);

  while (stream >> input) {
    inputs.push_back(input);
  }

  return inputs;
}

void test_inputs(std::string input_str) {
  input_list inputs = parse_inputs(input_str);
  ex_trace.clear();
  fprintf(stderr, "Calling unopt\n");
  p_unopt(inputs);
  ExceptionTrace trace_opt = ex_trace;

  ex_trace.clear();
  fprintf(stderr, "Calling opt\n");
  p_opt(inputs);
  ExceptionTrace trace_unopt = ex_trace;

  if (trace_opt != trace_unopt) {
    printf("INPUT\n%s\n", input_str.c_str());
    puts("UNOPT");
    print_trace(trace_unopt);
    puts("OPT");
    print_trace(trace_opt);
  }
}

int main(int argc, char* argv[]) {
  if (argc < 1) {
    puts("Inputs filename required");
    exit(EXIT_FAILURE);
  }

  char* inputs_filename = argv[1];
  std::ifstream inputs_file(inputs_filename);
  std::string line;
  while (std::getline(inputs_file, line)) {
    test_inputs(line);
  }
}
