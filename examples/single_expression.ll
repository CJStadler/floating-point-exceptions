; ModuleID = 'examples/single_expression.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [12 x i8] c"for x = %f\0A\00", align 1
@.str.1 = private unnamed_addr constant [33 x i8] c"0.5 / x * 0.5 + 2.0 / x = %.20f\0A\00", align 1
@.str.2 = private unnamed_addr constant [33 x i8] c"               2.25 / x = %.20f\0A\00", align 1

; Function Attrs: nounwind uwtable
define double @foo(double %x) #0 {
  %1 = alloca double, align 8
  %y = alloca double, align 8
  store double %x, double* %1, align 8
  %2 = load double, double* %1, align 8
  %3 = fdiv double 5.000000e-01, %2
  %4 = fmul double %3, 5.000000e-01
  %5 = load double, double* %1, align 8
  %6 = fdiv double 2.000000e+00, %5
  %7 = fadd double %4, %6
  store double %7, double* %y, align 8
  %8 = load double, double* %y, align 8
  ret double %8
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %x = alloca double, align 8
  %y = alloca double, align 8
  %yy = alloca double, align 8
  store double 1.000000e+03, double* %x, align 8
  %1 = load double, double* %x, align 8
  %2 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str, i32 0, i32 0), double %1)
  %3 = load double, double* %x, align 8
  %4 = call double @foo(double %3)
  store double %4, double* %y, align 8
  %5 = load double, double* %y, align 8
  %6 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.1, i32 0, i32 0), double %5)
  %7 = load double, double* %x, align 8
  %8 = fdiv double 2.250000e+00, %7
  store double %8, double* %yy, align 8
  %9 = load double, double* %yy, align 8
  %10 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.2, i32 0, i32 0), double %9)
  ret i32 0
}

declare i32 @printf(i8*, ...) #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1-24 (tags/RELEASE_381/final)"}
