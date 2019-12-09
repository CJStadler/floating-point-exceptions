import llvmlite
from typing import Any, Iterable

class ValueRef:
  name: str
  blocks: Iterable[ValueRef]
  instructions: Iterable[ValueRef]
  operands: Iterable[ValueRef]
  opcode: str
  arguments: Iterable[ValueRef]

class ModuleRef:
  functions: Iterable[ValueRef]

  def verify(self) -> None: ...

Target: Any

class ExecutionEngine:
  def add_module(self, mod: ModuleRef) -> None: ...
  def finalize_object(self) -> None: ...
  def run_static_constructors(self) -> None: ...

def initialize() -> None : ...
def initialize_native_target() -> None : ...
def initialize_native_asmprinter () -> None : ...

def parse_assembly(ir: str) -> llvmlite.binding.ModuleRef: ...

def create_mcjit_compiler(a: Any, b: Any) -> llvmlite.binding.ExecutionEngine:
  ...
