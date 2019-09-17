from subprocess import check_call, run

RTLIB_FILENAME = "rtlib.bc"
PASS_FILENAME = "build/report_exceptions/libReportExceptions.so"


def compile(source_filename, flags, out_filename):
    # Compile to IR
    ll_name = "temp.ll"
    check_call(["clang",
                "-S",
                "-emit-llvm",
                "-g",
                *flags,
                "-o",
                ll_name,
                source_filename])

    # Instrument
    instrumented = "temp-instrumented.ll"
    check_call(["opt",
                "-load",
                PASS_FILENAME,
                "-report_exceptions",
                "-o", instrumented,
                ll_name])

    # Compile to bc
    bc_name = "temp.bc"
    check_call(["opt", "-o", bc_name, instrumented])

    # Link with rtlib
    linked = "temp-linked.bc"
    check_call(["llvm-link-8", "-o", linked, RTLIB_FILENAME, bc_name])

    # Compile to object
    object = "temp.o"
    check_call(["llc-8", "--filetype=obj", "-o", object, linked])

    # Compile to executable
    check_call(["clang", "-lm", "-o", out_filename, object])


def test_with_flags(source_filename, flags):
    print("Compiling {} with {}".format(source_filename, flags))
    exe_filename = "temp.out"
    compile(source_filename, flags, exe_filename)
    run("./{}".format(exe_filename))