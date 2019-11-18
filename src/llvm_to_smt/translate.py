import operator
import llvmlite.binding as llvm
import z3
import re

from typing import Tuple, List, Dict

VAR_REGEX = re.compile(r"%[a-zA-Z0-9]+")
NUM_REGEX = re.compile(r"[0-9]+.[0-9]+e(\+|\-)[0-9]+")
ARG_REGEX = re.compile(r"(%s)|(%s)" % (VAR_REGEX.pattern, NUM_REGEX.pattern))
DBL_MAX = z3.RealVal("179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0")
DBL_MIN = z3.RealVal("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222507385850720138309023271733240406421921598046233183055332741688720443481391819585428315901251102056406733973103581100515243416155346010885601238537771882113077799353200233047961014744258363607192156504694250373420837525080665061665815894872049117996859163964850063590877011830487479978088775374994945158045160505091539985658247081864511353793580499211598108576")


class Condition:
    def __init__(self, name: str, instr: llvm.ValueRef, formula: z3.ArithRef):
        self.name = name
        self.instruction = instr
        self.formula = formula


class Solution:
    def __init__(self, sat: str, inputs: Dict[str, str],
                 condition: Condition, smt2: str):
        self.sat = sat
        self.inputs = inputs
        self.condition = condition
        self.smt2 = smt2


def parse_arg(arg: str) -> str:
    (type, name) = arg.split()
    if type != "double":
        raise RuntimeError("Unsupported type " + type)

    return name


def parse_param(match: Tuple[str, str, str]):
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


def parse_instruction(instruction: str) -> Tuple[str, str, str]:
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
                          param1: z3.ArithRef,
                          param2: z3.ArithRef) -> z3.ArithRef:
    """
    Translate an instruction for a binary operation into a z3 expression.
    """
    op = get_op(opcode)
    return op(param1, param2)


def solve(solver: z3.Solver, condition: Condition) -> Solution:
    solver.push()
    solver.add(condition.formula)

    sat = str(solver.check())
    if sat == "sat":
        model = solver.model()
        inputs = {str(n): model[n].as_decimal(20) for n in model.decls()}
    else:
        inputs = {}

    formula = solver.to_smt2()
    wrapped = "(push)\n%s(get-model)\n(pop)\n" % formula
    result = Solution(sat, inputs, condition, wrapped)

    solver.pop()
    return result


def abs(value: z3.ArithRef) -> z3.ArithRef:
    """Take the absolute value of an expression."""
    return z3.If(value >= 0, value, -value)


def check_division(instruction: str,
                   numerator: z3.ArithRef,
                   denominator: z3.ArithRef) -> List[Condition]:
    """
    Make conditions to check for an exception in a div.
    """
    denom_zero = denominator == 0
    invalid = Condition("invalid", instruction,
                        z3.And(numerator == 0, denom_zero))
    div_by_zero = Condition("div_by_zero", instruction,
                            z3.And(numerator != 0, denom_zero))
    overflow = Condition("overflow", instruction,
                         abs(numerator) > (abs(denominator) * DBL_MAX))
    underflow_formula = z3.And(abs(numerator) > 0,
                               abs(numerator) > (abs(denominator) * DBL_MAX))
    underflow = Condition("underflow", instruction, underflow_formula)

    conditions = [
        invalid,
        div_by_zero,
        overflow,
        underflow
    ]
    return conditions


def check_non_div(instruction: str, result: z3.ArithRef) -> List[Condition]:
    """
    Make conditions to check for an exception in a mul/add/sub.
    """
    absv = abs(result)
    overflow = Condition("overflow", instruction, absv > DBL_MAX)
    underflow = Condition("underflow", instruction,
                          z3.And(absv > 0, absv < DBL_MIN))
    conditions = [overflow, underflow]
    return conditions


def get_conditions(llvm_ast: llvm.ModuleRef) -> List[Condition]:
    """
    Get a list of z3 conditions. Each represents conditions on inputs which
    should trigger an exception somewhere in the program.
    """
    vars = {}
    conditions = []
    params = []

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
                    param1 = vars[param1]

                if isinstance(param2, str):
                    param2 = vars[param2]

                result = translate_instruction(opcode, param1, param2)
                vars[name] = result

                if opcode == 'fdiv':
                    conditions += check_division(instr, param1, param2)
                else:
                    conditions += check_non_div(instr, result)

    return (params, conditions)


def translate(llvm_ast: llvm.ModuleRef) -> str:
    """
    Construct an SMT2 formula from an llvm AST.
    """
    solver = z3.Solver()

    (params, conditions) = get_conditions(llvm_ast)

    # Require that each input be less than DBL_MAX.
    # These will apply to each exception condition.
    for param in params:
        solver.add(abs(param) < DBL_MAX)

    solutions = (solve(solver, condition) for condition in conditions)
    smt2s = []

    for solution in solutions:
        print("Checking for %s in" % solution.condition.name)
        print(solution.condition.instruction)

        for name, value in solution.inputs.items():
            print("%s = %s" % (name, value))
        print()

        smt2s.append(solution.smt2)

    smt2 = "\n".join(smt2s)
    smt2 = "(set-option :pp.decimal true)\n" + \
           "(set-option :pp.decimal_precision 20)\n" + \
           smt2

    return smt2
