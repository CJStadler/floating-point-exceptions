#include <stdio.h>
#include <vector>
#include <string>

enum ExceptionType {overflow, underflow, div_by_zero, invalid};

std::string type_string(ExceptionType type);

struct FPException {
  enum ExceptionType type;
  int lineno;
};

typedef std::vector<FPException> ExceptionTrace;

bool operator==(const FPException& lhs, const FPException& rhs);

void print_trace(FILE* file, ExceptionTrace trace);
