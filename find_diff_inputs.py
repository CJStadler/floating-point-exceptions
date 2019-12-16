import os
import shutil
import subprocess

from find_inputs import find_inputs

THIS_DIR = os.path.dirname(__file__)
SEARCH_DIR = os.path.join(THIS_DIR, "search")


def compile_to_llvm(source_filename: str,
                    out_filename: str,
                    unroll_count: int,
                    ffast_math: bool) -> None:
    print("Compiling {} -> {} with ffast-math={}".
          format(source_filename, out_filename, ffast_math))

    flags = ["-S", "-emit-llvm", "-O1"]
    if ffast_math:
        flags.append("-ffast-math")
    subprocess.check_call(["clang",
                           *flags,
                           "-o",
                           out_filename,
                           source_filename])
    if unroll_count > 0:
        subprocess.check_call(["opt",
                               "-S",
                               "-loop-unroll",
                               "-unroll-count=%d" % unroll_count,
                               "-o", out_filename,
                               out_filename])


def compile_search(program_filename: str,
                   function_name: str,
                   args_count: int) -> None:
    # The search makefile expects the program source to be in the search
    # directory, so we copy it.
    source = "source.tmp.c"
    shutil.copy(program_filename, os.path.join(SEARCH_DIR, source))

    subprocess.check_call([
        "make",
        "-C",
        SEARCH_DIR,
        "search.out",
        "SOURCE=%s" % source,
        "FUNCTION=%s" % function_name,
        "N=%d" % args_count])


def run_search(inputs_filename: str) -> None:
    subprocess.check_call([
        os.path.join(SEARCH_DIR, "search.out"),
        os.path.abspath(inputs_filename)
    ], stderr=subprocess.DEVNULL)


def main(program_filename: str, unroll_count: int) -> None:
    # Compile P and P'
    unopt_filename = "unopt.ll"
    compile_to_llvm(program_filename, unopt_filename, unroll_count, False)
    opt_filename = "opt.ll"
    compile_to_llvm(program_filename, opt_filename, unroll_count, True)

    # Solve for candidate inputs
    inputs_filename = "inputs.tmp.txt"
    (function_name, args_count) = find_inputs(unopt_filename, opt_filename,
                                              inputs_filename)

    # Compile search program
    compile_search(program_filename, function_name, args_count)

    # Run search program
    run_search(inputs_filename)


if __name__ == "__main__":
    import argparse
    description = "Find inputs that have different exception triggering " \
                  "behavior in a program optimized with fast math floating " \
                  "point operations."
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--unroll-count", type=int, default=0,
                        help="Iterations of loops to unroll.")
    parser.add_argument("program", type=str,
                        help="Filename of C program.")

    args = parser.parse_args()
    main(args.program, args.unroll_count)
