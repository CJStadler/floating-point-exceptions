import struct
import operator
import llvmlite.binding as llvm
import z3
import re

from typing import Tuple, Dict, Union, Set, List

VAR_REGEX = re.compile(r"%[a-zA-Z0-9]+")
NUM_REGEX = re.compile(r"[0-9]+.[0-9]+e(\+|\-)[0-9]+")
HEX_REGEX = re.compile(r"0x[0-9a-fA-F]+")
ARG_REGEX = re.compile(r"(%s)|(%s)|(%s)" % (VAR_REGEX.pattern,
                                            NUM_REGEX.pattern,
                                            HEX_REGEX.pattern))

DBL_MAX = z3.RealVal("179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0") # noqa
DBL_MIN = z3.RealVal("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222507385850720138309023271733240406421921598046233183055332741688720443481391819585428315901251102056406733973103581100515243416155346010885601238537771882113077799353200233047961014744258363607192156504694250373420837525080665061665815894872049117996859163964850063590877011830487479978088775374994945158045160505091539985658247081864511353793580499211598108576") # noqa

FloatArith = Union[float, z3.ArithRef]


class Constraint:
    def __init__(self, name: str, instr: str, formula: z3.ArithRef):
        self.name = name
        self.instruction = instr
        self.formula = formula

    def _and(self, other: z3.ArithRef):
        return Constraint(
            self.name,
            self.instruction,
            z3.And(self.formula, other),
        )

    def __eq__(self, other) -> bool:
        # This ignores name and instruction
        return isinstance(other, Constraint) and \
               self.formula.eq(other.formula)

    def __hash__(self) -> int:
        # This ignores name and instruction
        return hash(self.formula)


class Solution:
    def __init__(self, sat: str, inputs: Dict[str, str],
                 constraint: Constraint):
        self.sat = sat
        self.inputs = inputs
        self.constraint = constraint


def parse_arg(arg: str) -> str:
    (type, name) = arg.split()
    if type != "double":
        raise RuntimeError("Unsupported type " + type)

    return name


def parse_param(match: Tuple[str, str, str, str]) -> Union[str, float]:
    """
    Our regex has 4 groups so we find the one that matched and parse
    appropriately.
    """
    (var, num1, num2, hex) = match
    if num1:
        return float(num1)
    elif num2:
        return float(num2)
    elif hex:
        raw = bytes.fromhex(hex[2:])
        # Big-endian: https://llvm.org/docs/LangRef.html#simple-constants
        (parsed,) = struct.unpack('>d', raw)
        return parsed
    else:
        return var


def parse_instruction(instruction: str) \
        -> Tuple[str, Union[str, float], Union[str, float]]:
    """
    Extract the name of the result variable and inputs from a string
    representing a single instruction.
    """
    matches = ARG_REGEX.findall(instruction)
    if len(matches) != 3:
        raise RuntimeError("Error parsing \"%s\"" % instruction)

    ((result, _, _, _), p1, p2) = matches

    return (result, parse_param(p1), parse_param(p2))


def get_op(opcode: str):
    if opcode == "fadd":
        return operator.add
    elif opcode == "fsub":
        return operator.sub
    elif opcode == "fmul":
        return operator.mul
    elif opcode == "fdiv":
        return operator.truediv
    else:
        raise RuntimeError("Unsupported opcode " + opcode)


def translate_instruction(opcode: str,
                          param1: FloatArith,
                          param2: FloatArith) -> z3.ArithRef:
    """
    Translate an instruction for a binary operation into a z3 expression.
    """
    op = get_op(opcode)
    return op(param1, param2)


def format_solution(solution: z3.RatNumRef) -> str:
    decimal_str = solution.as_decimal(20)
    # Z3 puts a question mark at the end if the decimal is not exact, so we
    # strip it.
    return decimal_str.rstrip("?")


def solve(constraint: Constraint) -> Solution:
    solver = z3.Solver()
    solver.add(constraint.formula)

    sat = str(solver.check())
    if sat == "sat":
        model = solver.model()
        inputs = {str(n): format_solution(model[n]) for n in model.decls()}
    else:
        inputs = {}

    result = Solution(sat, inputs, constraint)

    return result


def abs(value: FloatArith) -> FloatArith:
    """Take the absolute value of an expression."""
    return z3.If(value >= 0, value, -value)


def check_division(instruction: str,
                   numerator: FloatArith,
                   denominator: FloatArith) -> Set[Constraint]:
    """
    Make constraints to check for an exception in a div.
    """
    denom_zero = denominator == 0
    invalid = Constraint(
        "invalid",
        instruction,
        z3.And(numerator == 0, denom_zero)
    )
    div_by_zero = Constraint(
        "div_by_zero",
        instruction,
        z3.And(numerator != 0, denom_zero)
    )
    overflow = Constraint(
        "overflow",
        instruction,
        abs(numerator) > (abs(denominator) * DBL_MAX)
    )
    underflow_formula = z3.And(abs(numerator) > 0,
                               abs(numerator) > (abs(denominator) * DBL_MAX))
    underflow = Constraint("underflow", instruction, underflow_formula)

    constraints = {
        invalid,
        div_by_zero,
        overflow,
        underflow
    }
    return constraints


def check_non_div(instruction: str, result: z3.ArithRef) -> Set[Constraint]:
    """
    Make constraints to check for an exception in a mul/add/sub.
    """
    absv = abs(result)
    overflow = Constraint("overflow", instruction, absv > DBL_MAX)
    underflow = Constraint(
        "underflow",
        instruction,
        z3.And(absv > 0, absv < DBL_MIN)
    )
    constraints = {overflow, underflow}
    return constraints


def make_constraints(llvm_ast: llvm.ModuleRef) \
        -> Tuple[str, List[str], Set[Constraint]]:
    """
    Get a list of z3 constraints. Each represents constraints on inputs which
    should trigger an exception somewhere in the program.
    """
    # References to all identifiers
    vars = {}  # type: Dict[str, z3.ArithRef]
    constraints = set()  # type: Set[Constraint]
    formals = []  # type: List[str]
    param_constraint = z3.BoolVal(True)

    function_name = None
    for function in llvm_ast.functions:
        if function_name:
            raise RuntimeError("Only one function supported")
        else:
            function_name = function.name

        # Declare an unimplemented function for each arg and assert that
        # it is less than DBL_MAX.
        for arg in function.arguments:
            name = parse_arg(arg.__str__())
            formals.append(name)
            z3_param = z3.Real(name)
            vars[name] = z3_param
            param_constraint = z3.And(param_constraint,
                                      abs(z3_param) < DBL_MAX)

        for block in function.blocks:
            for instruction in block.instructions:
                opcode = instruction.opcode
                if opcode not in ["fmul", "fdiv", "fadd", "fsub"]:
                    if opcode != "ret":
                        print("Unknown operation \"%s\", ignoring" % opcode)
                    continue

                instr = instruction.__str__()
                (name, param1, param2) = parse_instruction(instr)

                if isinstance(param1, str):
                    p1_ref = vars[param1]  # type: FloatArith
                else:
                    p1_ref = param1

                if isinstance(param2, str):
                    p2_ref = vars[param2]  # type: FloatArith
                else:
                    p2_ref = param2

                result = translate_instruction(opcode, p1_ref, p2_ref)
                vars[name] = result

                if opcode == 'fdiv':
                    constraints |= check_division(instr, p1_ref, p2_ref)
                else:
                    constraints |= check_non_div(instr, result)

    if function_name:
        constraints_with_params = {c._and(param_constraint)
                                   for c in constraints}
        return (function_name, formals, constraints_with_params)
    else:
        raise RuntimeError("No function found")
