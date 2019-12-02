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

struct InputResult {
  input_list inputs;
  ExceptionTrace unopt_trace;
  ExceptionTrace opt_trace;
  bool diff;
};

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

InputResult test_inputs(input_list inputs) {
  InputResult result;
  result.inputs = inputs;
  fprintf(stderr, "Testing inputs\n");
  print_inputs(stderr, inputs);

  ex_trace.clear();
  fprintf(stderr, "Calling unopt\n");
  double r_unopt = p_unopt(inputs);
  fprintf(stderr, "%.20e\n", r_unopt);
  result.unopt_trace = ex_trace;

  ex_trace.clear();
  fprintf(stderr, "Calling opt\n");
  double r_opt = p_opt(inputs);
  fprintf(stderr, "%.20e\n", r_opt);
  result.opt_trace = ex_trace;

  result.diff = result.unopt_trace != result.opt_trace;

  return result;
}

double incr(double input, double dir) {
  return nextafter(input, dir);
}

// Pick which result is "better".
InputResult best(InputResult a, InputResult b) {
  if (a.diff) {
    return a;
  } else if (b.diff) {
    return b;
  } else if (b.unopt_trace.size() > a.unopt_trace.size()) {
    return b;
  } else if (b.opt_trace.size() > a.opt_trace.size()) {
    return b;
  } else {
    return a;
  }
}

InputResult search_arg(input_list inputs, uint arg_id) {
  if (arg_id == inputs.size()) {
    // Base case: test the input.
    return test_inputs(inputs);
  } else {
    input_list high_inputs = inputs;
    input_list low_inputs = inputs;

    InputResult result;
    result.diff = false;
    uint i;
    for (i = 0; i < 1 + (SEARCH_RANGE * 2) && !result.diff; i++) {
      // Alternate searching up and down.
      bool up = (i % 2) == 0;

      /* In the up case we test then increment, so that we start with the given
       * inputs. In the down case we first increment so that we don't re-test
       * the given inputs. */
      if (up) {
        result = best(result, search_arg(high_inputs, arg_id + 1));

        // Increment this arg.
        if (!result.diff) {
          high_inputs[arg_id] = incr(high_inputs[arg_id], DBL_MAX);
        }
      } else {
        // Decrement this arg.
        if (!result.diff) {
          low_inputs[arg_id] = incr(low_inputs[arg_id], -DBL_MAX);
        }

        result = best(result, search_arg(low_inputs, arg_id + 1));
      }
    }

    return result;
  }
}

int main(int argc, char* argv[]) {
  if (argc < 1) {
    puts("Inputs filename required");
    exit(EXIT_FAILURE);
  }

  int n_inputs = 0;
  int unopt_ex_count = 0;
  int opt_ex_count = 0;
  int diff_count = 0;

  char* inputs_filename = argv[1];
  std::ifstream inputs_file(inputs_filename);
  std::string line;
  while (std::getline(inputs_file, line)) {
    n_inputs += 1;
    input_list inputs = parse_inputs(line);
    InputResult result = search_arg(inputs, 0);

    if (result.unopt_trace.size() > 0) unopt_ex_count += 1;
    if (result.opt_trace.size() > 0) opt_ex_count += 1;
    if (result.diff) {
      diff_count += 1;
      fprintf(stdout, "Input: ");
      print_inputs(stdout, result.inputs);
      fprintf(stdout, "P:  ");
      print_trace(stdout, result.unopt_trace);
      fprintf(stdout, "P': ");
      print_trace(stdout, result.opt_trace);
    }
  }

  fprintf(stdout, "Inputs:          %d\n", n_inputs);
  fprintf(stdout, "Exception in P:  %d\n", unopt_ex_count);
  fprintf(stdout, "Exception in P': %d\n", opt_ex_count);
  fprintf(stdout, "Diff producing:  %d\n", diff_count);
}
