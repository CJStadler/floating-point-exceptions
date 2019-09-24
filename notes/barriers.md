# Optimization barriers/fences

- `asm volatile(""::: "memory")` does not stop LLVM from combining
  instructions across it.
- `fence`: https://llvm.org/docs/LangRef.html#fence-instruction
  - Does not prevent combining instructions.
- https://llvm.org/docs/LangRef.html#constrainedfp
