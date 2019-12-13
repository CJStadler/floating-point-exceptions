#include <vector>

extern "C" {
  double target_fun_unopt(double, double);
  double target_fun_opt(double, double);
}

double p_unopt(std::vector<double> inputs) {
  return target_fun_unopt(inputs.at(0), inputs.at(1));
}

double p_opt(std::vector<double> inputs) {
  return target_fun_opt(inputs.at(0), inputs.at(1));
}
