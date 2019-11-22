import operator
import llvmlite.binding as llvm
import z3
import re

from typing import Tuple, List, Dict, Union, Set

VAR_REGEX = re.compile(r"%[a-zA-Z0-9]+")
NUM_REGEX = re.compile(r"[0-9]+.[0-9]+e(\+|\-)[0-9]+")
ARG_REGEX = re.compile(r"(%s)|(%s)" % (VAR_REGEX.pattern, NUM_REGEX.pattern))

DBL_MAX = z3.RealVal("179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0") # noqa
DBL_MIN = z3.RealVal("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222507385850720138309023271733240406421921598046233183055332741688720443481391819585428315901251102056406733973103581100515243416155346010885601238537771882113077799353200233047961014744258363607192156504694250373420837525080665061665815894872049117996859163964850063590877011830487479978088775374994945158045160505091539985658247081864511353793580499211598108576") # noqa

FloatArith = Union[float, z3.ArithRef]


class Constraint:
    def __init__(self, name: str, instr: str, formula: z3.ArithRef):
        self.name = name
        self.instruction = instr
        self.formula = formula


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


def parse_param(match: Tuple[str, str, str]) -> Union[str, float]:
    """
    Our regex has 3 groups so we find the one that matched. If it was one of
    the number groups then parse it as a float.
    """
    (var, num1, num2) = match
    if num1:
        return float(num1)
    elif num2:
        return float(num2)
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

    ((result, _, _), p1, p2) = matches

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


def solve(solver: z3.Solver, constraint: Constraint) -> Solution:
    solver.push()
    solver.add(constraint.formula)

    sat = str(solver.check())
    if sat == "sat":
        model = solver.model()
        inputs = {str(n): format_solution(model[n]) for n in model.decls()}
    else:
        inputs = {}

    result = Solution(sat, inputs, constraint)

    solver.pop()
    return result


def abs(value: FloatArith) -> FloatArith:
    """Take the absolute value of an expression."""
    return z3.If(value >= 0, value, -value)


def check_division(instruction: str,
                   numerator: FloatArith,
                   denominator: FloatArith) -> List[Constraint]:
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

    constraints = [
        invalid,
        div_by_zero,
        overflow,
        underflow
    ]
    return constraints


def check_non_div(instruction: str, result: z3.ArithRef) -> List[Constraint]:
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
    constraints = [overflow, underflow]
    return constraints


def get_constraints(llvm_ast: llvm.ModuleRef) \
        -> Tuple[List[z3.ArithRef], List[Constraint]]:
    """
    Get a list of z3 constraints. Each represents constraints on inputs which
    should trigger an exception somewhere in the program.
    """
    vars = {}  # type: Dict[str, z3.ArithRef]
    constraints = []  # type: List[Constraint]
    params = []  # type: List[z3.ArithRef]

    first = True
    for function in llvm_ast.functions:
        if not first:
            raise RuntimeError("Only one function supported")
        else:
            first = False

        # Declare an unimplemented function for each arg and assert that
        # it is less than DBL_MAX.
        for arg in function.arguments:
            name = parse_arg(arg.__str__())
            z3_param = z3.Real(name)
            params.append(z3_param)
            vars[name] = z3_param

        for block in function.blocks:
            for instruction in block.instructions:
                opcode = instruction.opcode
                if opcode == "ret":
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
                    constraints += check_division(instr, p1_ref, p2_ref)
                else:
                    constraints += check_non_div(instr, result)

    return (params, constraints)


def find_inputs(llvm_ast: llvm.ModuleRef) -> Set[Tuple[str, ...]]:
    """
    Find inputs that should trigger exceptions.
    """
    inputs = set()  # type: Set[Tuple[str, ...]]
    solver = z3.Solver()

    (params, constraints) = get_constraints(llvm_ast)

    # Require that each input be less than DBL_MAX.
    # These will apply to each exception constraint.
    for param in params:
        solver.add(abs(param) < DBL_MAX)

    solutions = (solve(solver, constraint) for constraint in constraints)

    for solution in solutions:
        print("Checking for %s in" % solution.constraint.name)
        print(solution.constraint.instruction)

        if solution.sat == "sat":
            param_vals = []

            for param in params:
                param_name = str(param)
                value = solution.inputs[param_name]
                print("%s = %s" % (param_name, value))
                param_vals.append(value)

            inputs.add(tuple(param_vals))
        else:
            print(solution.sat)

        print()

    return inputs
