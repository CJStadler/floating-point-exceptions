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

/*
 * Floating point exception handler.
 *
 * Prints the type of exception and exits.
 */
void catch_fpe(int sig, siginfo_t *info, void *secret) {
  puts("Caught floating point exception");

  int exception_code = info->si_code;

  // See http://man7.org/linux/man-pages/man2/sigaction.2.html for definitions
  // of these codes.
  if (exception_code == FPE_FLTOVF) {
    puts("Overflow");
  } else if (exception_code == FPE_FLTUND) {
    puts("Underflow");
  } else if (exception_code == FPE_FLTRES) {
    puts("Inexact");
  } else if (exception_code == FPE_FLTDIV) {
    puts("Division by zero");
  } else if (exception_code == FPE_FLTINV) {
    puts("Invalid");
  } else {
    puts("Unknown exception type");
  }

  puts("Exiting");
  exit(EXIT_FAILURE);
}

// Enable floating point exceptions and register signal handler before executing
// main().
__attribute__((constructor)) void register_checkpoint_signal_handler() {
  // Construct signal handler.
  // https://www.linuxjournal.com/files/linuxjournal.com/linuxjournal/articles/063/6391/6391l3.html
  struct sigaction sa;
  sa.sa_sigaction = (void *)catch_fpe;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_SIGINFO; // Pass the signal info to the handler.

  // Register signal handler
  sigaction(SIGFPE, &sa, NULL);

  // Enable all floating point exceptions.
  // https://www.gnu.org/software/libc/manual/html_node/Status-bit-operations.html
  feenableexcept(FE_ALL_EXCEPT);
}
