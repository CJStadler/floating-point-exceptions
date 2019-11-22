#include <vector>

enum ExceptionType {overflow, underflow, div_by_zero, invalid};

struct FPException {
  enum ExceptionType type;
  int lineno;
};

typedef std::vector<FPException> ExceptionTrace;
