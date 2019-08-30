#define _GNU_SOURCE

#include <fenv.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

/*
 * This can be loaded when executing a binary to catch all floating point
 * exceptions.
 *
 * LD_PRELOAD=`pwd`/trap_exceptions.so <binary>
 */

void catch_fpe(int sig) {
  puts("Caught floating point exception");

  int flags = fetestexcept(FE_ALL_EXCEPT);

  if (flags & FE_OVERFLOW) {
    puts("Overflow");
  } else if (flags & FE_UNDERFLOW) {
    puts("Underflow");
  } else if (flags & FE_INEXACT) {
    puts("Inexact");
  } else if (flags & FE_DIVBYZERO) {
    puts("Division by zero");
  } else if (flags & FE_INVALID) {
    puts("Invalid");
  } else {
    puts("Specific error not detected");
  }

  puts("Exiting");
  exit(EXIT_FAILURE);
}

// Enable floating point exceptions and register signal handler.
__attribute__((constructor)) void register_checkpoint_signal_handler() {
  feenableexcept(FE_ALL_EXCEPT);
  signal(SIGFPE, catch_fpe);
}
