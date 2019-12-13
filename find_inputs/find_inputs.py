from typing import Tuple

from .parser import create_execution_engine, parse_file
from .solver import make_constraints, solve, Constraint, Solution


def solve_and_log(constraint: Constraint) -> Solution:
    solution = solve(constraint)
    print(".", end="", flush=True)
    return solution


def find_inputs(unopt_llvm_filename, opt_llvm_filename, inputs_filename) \
        -> Tuple[str, int]:
    llvm_engine = create_execution_engine()
    unopt_llvm_ast = parse_file(unopt_llvm_filename, llvm_engine)
    opt_llvm_ast = parse_file(opt_llvm_filename, llvm_engine)

    (function_name, formals, unopt_constraints) = \
        make_constraints(unopt_llvm_ast)
    print("Made %d constraints from %s" % (len(unopt_constraints),
                                           unopt_llvm_filename))
    (opt_function_name, opt_formals, opt_constraints) = \
        make_constraints(opt_llvm_ast)
    print("Made %d constraints from %s" % (len(opt_constraints),
                                           opt_llvm_filename))

    if function_name != opt_function_name:
        raise RuntimeError("Names of opt and unopt functions do not match")

    if formals != opt_formals:
        raise RuntimeError("Formals of opt and unopt do not match")

    constraints = unopt_constraints | opt_constraints
    print("%d constraints are unique" % len(constraints))

    print("Solving")
    solutions = (solve_and_log(constraint) for constraint in constraints)
    sat = [solution for solution in solutions if solution.sat == "sat"]
    print("")
    print("%d constraints are satisfiable" % len(sat))

    # Put inputs in the order expected by the function.
    inputs_lists = {tuple([solution.inputs[formal] for formal in formals])
                    for solution in sat}
    print("%d inputs are unique" % len(inputs_lists))

    with open(inputs_filename, "w") as f:
        for inputs in inputs_lists:
            f.write(" ".join(inputs))
            f.write("\n")
    print("Saved input solutions to %s" % inputs_filename)

    return (function_name, len(formals))


if __name__ == "__main__":
    import argparse
    description = "Generate inputs that are likely to trigger exceptions on " \
                  "a given program."
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("unopt_llvm_file", type=str,
                        help="Filename of LLVM IR of unoptimized program")
    parser.add_argument("opt_llvm_file", type=str,
                        help="Filename of LLVM IR of optimized program")
    parser.add_argument("inputs_file", type=str,
                        help="Name of file to output solutions (inputs to the "
                             "given program) to.")

    args = parser.parse_args()
    find_inputs(args.unopt_llvm_file, args.opt_llvm_file, args.inputs_file)
