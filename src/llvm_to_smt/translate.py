import operator
import llvmlite.binding as llvm
import z3
import re

from typing import Tuple, List

VAR_REGEX = re.compile("%[a-zA-Z0-9]+")


def parse_arg(arg: str) -> str:
    (type, name) = arg.split()
    if type != "double":
        raise RuntimeError("Unsupported type " + type)

    return name


def parse_instruction(instruction: str) -> Tuple[str, str, str]:
    (result, p1, p2) = VAR_REGEX.findall(instruction)
    return (result, p1, p2)


def get_op(opcode: str):
    if opcode == "fadd":
        operator.add
    elif opcode == "fsub":
        operator.sub
    else:
        raise RuntimeError("Unsupported opcode " + opcode)


def define_function(opcode: str, param1: z3.ArithRef, param2: z3.ArithRef) \
        -> z3.ArithRef:
    op = get_op(opcode)
    return op(param1, param2)


def check_instruction(solver,
                      opcode: str,
                      param1: z3.ArithRef,
                      param2: z3.ArithRef) -> List[str]:
    formulae = []

    solver.push()
    solver.pop()

    return formulae

def translate(llvm_ast: llvm.ModuleRef) -> List[str]:
    solver = z3.Solver()

    vars = {}
    smt2s = []

    first = True
    for function in llvm_ast.functions:
        if not first:
            raise RuntimeError("Only one function supported")
        else:
            first = False

        # Declare an unimplemented function for each arg.
        for arg in function.arguments:
            name = parse_arg(arg.__str__())
            z3_fun = z3.Real(name)
            vars[name] = z3_fun

        for block in function.blocks:
            for instruction in block.instructions:
                opcode = instruction.opcode
                (name, param1, param2) = \
                    parse_instruction(instruction.__str__())
                result = define_function(opcode, vars[param1], vars[param2])
                vars[name] = result
                formulae = check_instruction(solver,
                                             opcode,
                                             vars[param1],
                                             vars[param2])
                smt2s = smt2s + formulae

    return solver
