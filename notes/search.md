- Single input:
  - odometer
  - carbongas
  - coshestonc4 (other inputs are set constant in benchmark)
  - invarplanelat
  - invarplanelong
  - refract (reverse_saasta_refraction)
  - ssats
- Search -1 to 1
- Driver program iterates through interval and calls benchmark functions.
  - Calls unopt and opt functions?
- How to communicate between exception detector and driver?
  - Shared global struct: detector increments count whenever it detects an
    exception. Driver checks counts after every run.
- If we are only trying to find inputs that trigger any exception then there's
  no need to check after every operation, can just check after every run of the
target program.

## Results

- carbongas
  - Very small inputs trigger overflow (e.g. 1.0e-200)
```
$ ./search.out 2> carbongas.log
Running 1000000000 iterations
1000000000 had no exceptions
0 had exceptions in both
0 had exceptions only for opt
0 had exceptions only for unopt
```

- invarplanelat
  - Inputs in [-1, 1] unlikely to trigger exception because the first operation
    is to subtract a large number from it.
```
$ ./search.out 2> invarplanelat.log
Running 1000000000 iterations
1000000000 had no exceptions
0 had exceptions in both
0 had exceptions only for opt
0 had exceptions only for unopt
```

- invarplanelong
  - Similar to invarplanelat
```
$ ./search.out 2> invarplanelong.log
Running 1000000000 iterations
1000000000 had no exceptions
0 had exceptions in both
0 had exceptions only for opt
0 had exceptions only for unopt
```

- odometer
  - Very small number should trigger overflow.
```
$ ./search.out 2> odometer.log
Running 1000000 iterations
1000000 had no exceptions
0 had exceptions in both
0 had exceptions only for opt
0 had exceptions only for unopt
```
- ssats

## TODO

- Manually solve symbolically, then search in that range for diff between opt
  and unopt.
- Use examples from Ariadne paper and compare opt and unopt.
- DReal solver: approximate solutions to real constraints.
- C -> SMT?

## Symbolic execution

- KLEE now has a z3 backend. Does it use float or real?
- KLEE generates smt files: https://klee.github.io/docs/files/
- Then run dReal on the smt?
