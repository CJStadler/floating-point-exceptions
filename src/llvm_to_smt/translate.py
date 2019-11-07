import llvmlite.binding as llvm
import z3


def translate(llvm_ast: llvm.ModuleRef) -> z3.Solver:
    solver = z3.Solver()

    names = name_gen()

    first = True
    for function in llvm_ast.functions:
        if not first:
            raise RuntimeError("Only one function supported")
        else:
            first = False

        for block in function.blocks:
            for instruction in block.instructions:
                # This won't work, we need the actual name for when it is used.
                var_name = names.__next__()
                # This is the equivalent of declare-fun?
                # Do we want instead to define-fun?
                var = z3.Real(var_name)
                op = instruction.opcode

                for operand in instruction.operands:
                    pass
    return solver


def name_gen():
    i = 0

    while True:
        yield("v%i" % i)
        i += 1
