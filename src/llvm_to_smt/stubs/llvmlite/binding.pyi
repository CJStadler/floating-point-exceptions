import llvmlite
from typing import Any, Iterator

class ValueRef:
  name: str
  blocks: Iterator[ValueRef]
  instructions: Iterator[ValueRef]
  operands: Iterator[ValueRef]
  opcode: str

class ModuleRef:
  functions: Iterator[ValueRef]

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
