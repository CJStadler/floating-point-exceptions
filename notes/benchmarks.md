# Benchmarks


## Easy

- turbine1
  - straight line
  - only float
- turbine3
  - straight line
  - only float
- carbongas
  - straight line
  - only float
- coshestonc4
  - straight line
  - only float
  - Uses `exp` from math.h, which we should be able to approximate.
- jetengine
  - straight line
  - only float

## Math.h

- precess
  - straight line
  - only float
  - macro constants
  - requires `math.h`
- invarplanelat
  - straight line
  - only float
  - requires `math.h`
- invarplanelong
  - straight line
  - only float
  - requires `math.h`
  - uses macro constants
- pendulum
  - straight line
  - only float
  - requires `math.h`

## Loops

- odometer
  - only float (other than look index)
  - for loop (with constant bound)

## Complex

- plutoloc
  - conditionals
  - non-floats (including pointers)
  - macro constants
- refract
  - multiple functions
  - one function has a while loop with an int bound
  - macro constants
  - requires `math.h`
- ssats
  - structs
  - arrays
  - ints
  - requires `math.h`
- triton
  - multiple functions
  - ints
  - pointers
  - while loops
  - arrays
