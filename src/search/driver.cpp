#include <stdio.h>
#include <stdlib.h>
#include <float.h>
#include <fenv.h>
#include <math.h>

#include <random>
#include <vector>
#include <sstream>
#include <string>
#include <fstream>

#include "../report_exceptions_pass/fp_exception.hpp"

#define SEARCH_RANGE 3

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

bool test_inputs(input_list inputs) {
  ex_trace.clear();
  fprintf(stderr, "Calling unopt\n");
  double r_unopt = p_unopt(inputs);
  ExceptionTrace trace_opt = ex_trace;

  ex_trace.clear();
  fprintf(stderr, "Calling opt\n");
  double r_opt = p_opt(inputs);
  ExceptionTrace trace_unopt = ex_trace;

  if (trace_opt != trace_unopt) {
    puts("INPUTS");
    uint i;
    for (i = 0; i < inputs.size(); i++) {
      printf("%.20f ", inputs[i]);
    }
    puts("");
    puts("UNOPT");
    printf("%.20e\n", r_unopt);
    print_trace(trace_unopt);
    puts("OPT");
    printf("%.20e\n", r_opt);
    print_trace(trace_opt);

    return true;
  } else {
    return false;
  }
}

bool search_arg(input_list inputs, int arg_id) {
  input_list high_inputs = inputs;
  input_list low_inputs = inputs;

  // Increment the low input so that we don't test the starting inputs twice.
  low_inputs[arg_id] = nextafter(low_inputs[arg_id], -DBL_MAX);

  bool found = false;
  bool up = true; // Direction to search in on this iteration.
  int i;
  for (i = 0; i < SEARCH_RANGE && !found; i++) {
    if (up) {
      found = test_inputs(high_inputs);

      if (!found) {
        // Increment the other inputs.
        uint j;
        for (j = arg_id + 1; j < inputs.size() && !found; j++) {
          found = search_arg(high_inputs, j);
        }

        // Increment this input.
        if (!found) {
          high_inputs[arg_id] = nextafter(high_inputs[arg_id], DBL_MAX);
        }
      }
    } else {
      found = test_inputs(low_inputs);

      if (!found) {
        // Increment the other inputs.
        uint j;
        for (j = arg_id + 1; j < inputs.size() && !found; j++) {
          found = search_arg(low_inputs, j);
        }

        // Increment this input.
        if (!found) {
          low_inputs[arg_id] = nextafter(low_inputs[arg_id], -DBL_MAX);
        }
      }
    }

    // Switch the direction
    up = !up;
  }

  return found;
}

void search_around(std::string input_str) {
  input_list inputs = parse_inputs(input_str);
  search_arg(inputs, 0);
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
    search_around(line);
  }
}
