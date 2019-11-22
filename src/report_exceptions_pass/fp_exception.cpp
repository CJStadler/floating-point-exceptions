#include <stdio.h>
#include <vector>
#include <string>

enum ExceptionType {overflow, underflow, div_by_zero, invalid};

std::string type_string(ExceptionType type) {
  switch (type) {
    case overflow:
      return "Overflow";
    case underflow:
      return "Underflow";
    case div_by_zero:
      return "DivByZero";
    case invalid:
      return "Invalid";
  }
}

struct FPException {
  enum ExceptionType type;
  int lineno;
};

typedef std::vector<FPException> ExceptionTrace;

bool operator==(const FPException& lhs, const FPException& rhs)
{
    return (lhs.type == rhs.type) && (lhs.lineno == rhs.lineno);
}

void print_trace(ExceptionTrace trace) {
  int len = trace.size();
  for(int i = 0; i < len; i++) {
    FPException ex = trace.at(i);

    printf("line %d: %s\n", ex.lineno, type_string(ex.type).c_str());
  }
}
