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
