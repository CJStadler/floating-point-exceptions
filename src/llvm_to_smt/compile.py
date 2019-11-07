from parser import create_execution_engine, parse_file
from translate import translate


def compile(llvm_filename, smt2_filename) -> None:
    llvm_engine = create_execution_engine()
    llvm_ast = parse_file(llvm_filename, llvm_engine)
    z3_solver = translate(llvm_ast)
    smt2 = z3_solver.to_smt2()

    with open(smt2_filename) as f:
        f.write(smt2)


if __name__ == "__main__":
    import sys
    compile(sys.argv[1], sys.argv[2])
