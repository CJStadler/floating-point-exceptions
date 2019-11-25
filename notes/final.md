## Architecture
- Source is compiled to `P` and `P'` llvm programs
- Solver generates inputs from `P` and `P'`
- Instrument programs to generate exception traces
- Link programs to search driver
- Search:
  - For each input
    - 100 times
      - Run input on `P` and `P'` and get traces
      - Compare traces and record result
      - Get next input with `nextafter`

- Exception:
  - type
  - line number

- Use a `vector<Exception>` to represent trace.

- Range: iterations in each direction.
  - Range 0 means just test the given input.
  - E.g. Range 1 means increment up once and down once.

## Results

- turbine1
  - 22 inputs from P
  - range -> diff-producing inputs
    - 0 -> 4
    - 1 -> 13
    - 2 -> 13
    - 10 -> 13
