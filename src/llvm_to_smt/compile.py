from parser import create_execution_engine, parse_file
from solver import make_constraints, solve, Constraint, Solution


def solve_and_log(constraint: Constraint) -> Solution:
    solution = solve(constraint)
    print(".", end="", flush=True)
    return solution


def compile(unopt_llvm_filename, opt_llvm_filename, inputs_filename) -> None:
    llvm_engine = create_execution_engine()
    unopt_llvm_ast = parse_file(unopt_llvm_filename, llvm_engine)
    opt_llvm_ast = parse_file(opt_llvm_filename, llvm_engine)

    (formals, unopt_constraints) = make_constraints(unopt_llvm_ast)
    print("Made %d constraints from %s" % (len(unopt_constraints),
                                           unopt_llvm_filename))
    (opt_formals, opt_constraints) = make_constraints(opt_llvm_ast)
    print("Made %d constraints from %s" % (len(opt_constraints),
                                           opt_llvm_filename))

    if formals != opt_formals:
        raise RuntimeError("Formals of opt and unopt do not match")

    constraints = unopt_constraints | opt_constraints
    print("%d constraints are unique" % len(constraints))

    print("Solving")
    solutions = (solve_and_log(constraint) for constraint in constraints)
    sat = [solution for solution in solutions if solution.sat == "sat"]
    print("")
    print("%d constraints are satisfiable" % len(sat))

    with open(inputs_filename, "w") as f:
        for solution in sat:
            # Put inputs in the order expected by the function.
            inputs = [solution.inputs[formal] for formal in formals]
            f.write(" ".join(inputs))
            f.write("\n")
    print("Saved input solutions to %s" % inputs_filename)


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
    compile(args.unopt_llvm_file, args.opt_llvm_file, args.inputs_file)
