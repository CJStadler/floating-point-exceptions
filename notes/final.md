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

## Search

- "This input is unlikely to be a floating-
  point number, so we search the neighborhood of that input for a
  candidate floating point number that also triggers the exception over
  real arithmetic" (p2)
- Given a solution X Ariadne tests P with the FP numbers on either side of X. If
  neither of these yield an exception then it asks the SMT solver for a new
  solution. See Algorithm 5 (p8).

## Results

- turbine1
  - 3 parameters
  - 22 inputs from P
  - range -> diff-producing inputs
    - 0 -> 4
    - 1 -> 13
    - 2 -> 13
    - 10 -> 13

- turbine3
  - 3 parameters
  - 24 inputs from P
  - range -> diff-producing inputs
    - 0 -> 3
    - 1 -> 11
    - 2 -> 12
    - 10 -> 12

- jetengine
  - 2 parameters
  - 37 inputs from P
  - range -> diff-producing inputs
    - 50 -> 0

- carbongas
  - IR has a hex literal, need to work on parsing.

## TODO

- For inputs from P and P'
  - How many constraints?
  - How many SAT?
  - How many had an exception when tested?
  - How many diffs?
  - For each diff give the two traces

- Compress log: just input and sequence
- Number of satisfying assignments different?

- Write down high level algorithm.
