# Floating point exception catcher

This contains a tool which will catch any floating point exceptions in a
program, report the type of exception, and exit the program. An example program
for each type of exception is also provided.

`src/trap_exceptions.c` is compiled into a shared object file. Using
`LD_PRELOAD` this can be loaded with a binary to catch any floating point
exceptions.

Example:

```
$ make
clang -lm -shared -fPIC -o trap_exceptions.so src/trap_exceptions.c
$ make overflow.out
clang -o overflow.out src/overflow.c
$ LD_PRELOAD=`pwd`/trap_exceptions.so ./overflow.out 
Caught floating point exception
Overflow
Exiting
```
