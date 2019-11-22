from parser import create_execution_engine, parse_file
from solver import find_inputs


def compile(llvm_filename, inputs_filename) -> None:
    llvm_engine = create_execution_engine()
    llvm_ast = parse_file(llvm_filename, llvm_engine)
    inputs = find_inputs(llvm_ast)
    input_strs = (" ".join(params) for params in inputs)

    with open(inputs_filename, "w") as f:
        for input in input_strs:
            f.write(input)
            f.write("\n")


if __name__ == "__main__":
    import sys
    compile(sys.argv[1], sys.argv[2])
