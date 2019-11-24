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

## Results
- Searching with range 2 finds 17 inputs that produce different traces.
  - Out of 22 inputs.
