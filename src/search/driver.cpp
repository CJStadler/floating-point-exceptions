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

#define SEARCH_RANGE 0

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

void print_inputs(FILE* file, input_list inputs) {
  uint i;
  for (i = 0; i < inputs.size(); i++) {
    if (i > 0) {
      fprintf(file, " ");
    }
    fprintf(file, "%.20e", inputs[i]);
  }
  fprintf(file, "\n");
}

bool test_inputs(input_list inputs) {
  fprintf(stderr, "Testing inputs\n");
  print_inputs(stderr, inputs);

  ex_trace.clear();
  fprintf(stderr, "Calling unopt\n");
  double r_unopt = p_unopt(inputs);
  fprintf(stderr, "%.20e\n", r_unopt);
  ExceptionTrace trace_opt = ex_trace;

  ex_trace.clear();
  fprintf(stderr, "Calling opt\n");
  double r_opt = p_opt(inputs);
  fprintf(stderr, "%.20e\n", r_opt);
  ExceptionTrace trace_unopt = ex_trace;

  bool diff = trace_opt != trace_unopt;

  if (diff) {
    print_inputs(stdout, inputs);
  }

  return diff;
}

double incr(double input, double dir) {
  return nextafter(input, dir);
}

bool search_arg(input_list inputs, uint arg_id) {
  if (arg_id == inputs.size()) {
    // Base case: test the input.
    return test_inputs(inputs);
  } else {
    input_list high_inputs = inputs;
    input_list low_inputs = inputs;

    bool found = false;
    uint i;
    for (i = 0; i < 1 + (SEARCH_RANGE * 2) && !found; i++) {
      // Alternate searching up and down.
      bool up = (i % 2) == 0;

      /* In the up case we test then increment, so that we start with the given
       * inputs. In the down case we first increment so that we don't re-test
       * the given inputs. */
      if (up) {
        found = search_arg(high_inputs, arg_id + 1);

        // Increment this arg.
        if (!found) {
          high_inputs[arg_id] = incr(high_inputs[arg_id], DBL_MAX);
        }
      } else {
        // Decrement this arg.
        if (!found) {
          low_inputs[arg_id] = incr(low_inputs[arg_id], -DBL_MAX);
        }

        found = search_arg(low_inputs, arg_id + 1);
      }
    }

    return found;
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
    input_list inputs = parse_inputs(line);
    bool found = search_arg(inputs, 0);

    if (found) {
      fprintf(stderr, "Found diff while searching\n");
      print_inputs(stderr, inputs);
    }
  }
}
