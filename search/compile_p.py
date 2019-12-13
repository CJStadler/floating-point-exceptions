import argparse
import subprocess

from pathlib import Path

RTLIB_FILENAME = "../rtlib.bc"
PASS_FILENAME = "../libReportExceptions.so"
UNOPT_OBJ = "unopt.o"
OPT_OBJ = "opt.o"
CLANG_FLAGS = ["-Xclang", "-disable-O0-optnone"]
LLVM_FLAGS = ["-instcombine"]


def compile(source_filename, out_filename, ffast_math=False):
    print("Compiling {} -> {} with ffast-math={}".
          format(source_filename, out_filename, ffast_math))
    # Compile to IR
    ll_name = "temp.ll"

    flags = CLANG_FLAGS
    if ffast_math:
        flags += ["-ffast-math"]
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
                           *LLVM_FLAGS,
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
    subprocess.check_call(["llc-8",
                           "--filetype=obj",
                           "-o",
                           out_filename,
                           linked])


def _check_file(filename):
    if not Path(filename).is_file():
        msg = "{} not found. You must compile it first.".format(filename)
        raise RuntimeError(msg)


def main():
    description = "Compile a program into unoptimized and optimized objects."
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("source_filename",
                        help="The C source file to compile.")

    args = parser.parse_args()

    compile(args.source_filename, UNOPT_OBJ, ffast_math=False)
    compile(args.source_filename, OPT_OBJ, ffast_math=True)


if __name__ == "__main__":
    main()
