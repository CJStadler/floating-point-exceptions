import argparse
import subprocess

from pathlib import Path

RTLIB_FILENAME = "rtlib.bc"
PASS_FILENAME = "build/report_exceptions/libReportExceptions.so"
UNOPT_EXE = "unopt.out"
OPT_EXE = "opt.out"
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
    object = "temp.o"
    subprocess.check_call(["llc-8", "--filetype=obj", "-o", object, linked])

    # Compile to executable
    subprocess.check_call(["clang", "-lm", "-o", out_filename, object])


def run(exe_filename, arguments, save_trace=False):
    _check_file(exe_filename)
    args_string = " ".join(arguments)
    command = "./{}".format(exe_filename)
    print("Running \"{} {}\"".format(command, args_string))
    proc = subprocess.run([command, args_string],
                          stderr=subprocess.PIPE,
                          stdout=subprocess.PIPE)

    trace = proc.stderr.decode('utf-8')

    if save_trace:
        trace_filename = exe_filename + ".trace"
        print("Writing trace to {}".format(trace_filename))
        with open(trace_filename, "w") as f:
            f.write(trace)
    else:
        print(trace)


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
                        help="Execute the two programs",
                        action="store_true")
    parser.add_argument("-s", "--save",
                        help="Save the traces to files instead of printing",
                        action="store_true")
    parser.add_argument("args", nargs=argparse.REMAINDER,
                        help="Arguments to pass to the program. Only used if \
                        --run is set.")

    args = parser.parse_args()

    if args.compile:
        source_filename = args.compile
        compile(source_filename, UNOPT_EXE, ffast_math=False)
        compile(source_filename, OPT_EXE, ffast_math=True)

    if args.run:
        run(UNOPT_EXE, args.args, save_trace=args.save)
        run(OPT_EXE, args.args, save_trace=args.save)


if __name__ == "__main__":
    main()
