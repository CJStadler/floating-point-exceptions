from typing import Iterable, Union

# Many functions accept either an ArithRef or a constant.
BoolArith = Union[bool, ArithRef]
FloatArith = Union[float, ArithRef]

class Solver:
    def push(self) -> None: ...
    def pop(self) -> None: ...
    def add(self, ArithRef) -> None: ...
    def check(self) -> CheckSatResult: ...
    def model(self) -> ModelRef: ...

class ArithRef:
    def __mul__(self, other: FloatArith) -> ArithRef: ...
    def __rmul__(self, other: FloatArith) -> ArithRef: ...
    def __neg__(self) -> ArithRef: ...
    def __gt__(self, other: FloatArith) -> ArithRef: ...
    def __ge__(self, other: FloatArith) -> ArithRef: ...
    def __lt__(self, other: FloatArith) -> ArithRef: ...
    def __le__(self, other: FloatArith) -> ArithRef: ...
    def eq(self, other) -> bool: ...

class ModelRef:
    def decls(self) -> Iterable[ArithRef]: ...
    def __getitem__(self, idx: Union[int, ArithRef]) -> RatNumRef: ...

class RatNumRef(ArithRef):
    def as_decimal(self, precision: int) -> str: ...

class CheckSatResult: ...

def Real(name: str) -> ArithRef: ...

def RealVal(repr: str) -> RatNumRef: ...
def BoolVal(val: bool) -> ArithRef: ...

def And(a: BoolArith, b: BoolArith) -> ArithRef: ...
def If(cond: BoolArith, xthen: FloatArith, xelse: FloatArith) -> ArithRef: ...

