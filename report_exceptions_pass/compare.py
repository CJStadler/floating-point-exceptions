import argparse
import subprocess

from pathlib import Path

RTLIB_FILENAME = "rtlib.bc"
PASS_FILENAME = "build/report_exceptions/libReportExceptions.so"
UNOPT_EXE = "unopt.out"
OPT_EXE = "opt.out"
UNOPT_FLAGS = ["-O1"]
OPT_FLAGS = ["-O1", "-ffast-math"]


def compile(source_filename, flags, out_filename):
    print("Compiling {} -> {} with flags {}".
          format(source_filename, out_filename, flags))
    # Compile to IR
    ll_name = "temp.ll"
    subprocess.check_call(["clang",
                           "-S",
                           "-emit-llvm",
                           "-g",
                           *flags,
                           "-o",
                           ll_name,
                           source_filename])

    # Instrument
    _check_file(PASS_FILENAME)
    instrumented = "temp-instrumented.ll"
    subprocess.check_call(["opt",
                           "-load",
                           PASS_FILENAME,
                           "-report_exceptions",
                           "-o", instrumented,
                           ll_name])

    # Compile to bc
    bc_name = "temp.bc"
    subprocess.check_call(["opt", "-o", bc_name, instrumented])

    # Link with rtlib
    _check_file(RTLIB_FILENAME)
    linked = "temp-linked.bc"
    subprocess.check_call(["llvm-link-8",
                           "-o",
                           linked,
                           RTLIB_FILENAME,
                           bc_name])

    # Compile to object
    object = "temp.o"
    subprocess.check_call(["llc-8", "--filetype=obj", "-o", object, linked])

    # Compile to executable
    subprocess.check_call(["clang", "-lm", "-o", out_filename, object])


def run(exe_filename, arguments):
    _check_file(exe_filename)
    args_string = " ".join(arguments)
    command = "./{}".format(exe_filename)
    print("Running \"{} {}\"".format(command, args_string))
    proc = subprocess.run([command, args_string],
                          stderr=subprocess.PIPE,
                          stdout=subprocess.PIPE)
    print(proc.stderr.decode('utf-8'))


def _check_file(filename):
    if not Path(filename).is_file():
        msg = "{} not found. You must compile it first.".format(filename)
        raise RuntimeError(msg)


def main():
    parser = argparse.ArgumentParser(
        description="Compare a program with and without ffast-math.")
    parser.add_argument("-c", "--compile",
                        help="The C source file to compile. If this option is \
                              not set we assume it has already been compiled.")
    parser.add_argument("-r", "--run",
                        help="Execute the two programs with the given args. \
                              If this is not set we will compile without \
                              executing")

    args = parser.parse_args()

    if args.compile:
        source_filename = args.compile
        compile(source_filename, UNOPT_FLAGS, UNOPT_EXE)
        compile(source_filename, OPT_FLAGS, OPT_EXE)

    if args.run is not None:
        exe_args = args.run
        run(UNOPT_EXE, exe_args)
        run(OPT_EXE, exe_args)


if __name__ == "__main__":
    main()
