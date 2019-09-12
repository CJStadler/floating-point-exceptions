Hi Thomas,

I've realized that my approach to detecting exceptions won't work for
constructing a trace of all exceptions in a program. My implementation triggered
signals for FP exceptions, trapped the first exception and then exited the
program. To construct a trace I was planning on modifying this to resume the
program after each exception. The issue with this is that when the program is
resumed the operation which triggered the exception will not have completed.
E.g. in the program

double x = 1;
x = x + DBL_MAX;
printf("x = %f", x);

If you trap the overflow exception and then resume the program "x = 1" will be
printed instead of "x = inf".

My plan now is to instead instrument the program to detect each exception after
it occurs. After every floating point operation we would check whether the
result is an exception, and if so print it. For example, we would add code like
"if x == INFINITY then print("Overflow")". Does this seem like a reasonable
approach, or do you have any other suggestions?

I also have a concern about what exception traces should be considered
equivalent. In the function

double add_two(double x) {
    x += 1;
    x += 1;
    return x;
}

If "x == DBL_MAX" then both operations would overflow. If "x == DBL_MAX - 1"
then only the second operation would overflow. But if this is optimized into a
single operation then there would only be one overflow in both cases. Should P
and P' be considered equivalent in this case? This isn't an urgent question so
we can discuss it at our next meeting if you'd prefer.

Best,
Chris
