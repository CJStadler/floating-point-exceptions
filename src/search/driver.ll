; ModuleID = 'driver.cpp'
source_filename = "driver.cpp"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%"class.std::linear_congruential_engine" = type { i64 }
%"class.std::normal_distribution" = type <{ %"struct.std::normal_distribution<double>::param_type", double, i8, [7 x i8] }>
%"struct.std::normal_distribution<double>::param_type" = type { double, double }
%"struct.std::__detail::_Adaptor" = type { %"class.std::linear_congruential_engine"* }

$_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEC2IKdvEERT_ = comdat any

$_ZNSt19normal_distributionIdEC2Edd = comdat any

$_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_ = comdat any

$_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE4seedEm = comdat any

$_ZNSt8__detail5__modImLm2147483647ELm1ELm0EEET_S1_ = comdat any

$_ZNSt8__detail4_ModImLm2147483647ELm1ELm0ELb1ELb1EE6__calcEm = comdat any

$_ZNSt19normal_distributionIdE10param_typeC2Edd = comdat any

$_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_RKNS0_10param_typeE = comdat any

$_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEC2ERS2_ = comdat any

$_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEclEv = comdat any

$_ZNKSt19normal_distributionIdE10param_type6stddevEv = comdat any

$_ZNKSt19normal_distributionIdE10param_type4meanEv = comdat any

$_ZSt18generate_canonicalIdLm53ESt26linear_congruential_engineImLm16807ELm0ELm2147483647EEET_RT1_ = comdat any

$_ZSt3minImERKT_S2_S2_ = comdat any

$_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3maxEv = comdat any

$_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3minEv = comdat any

$_ZSt3loge = comdat any

$_ZSt3maxImERKT_S2_S2_ = comdat any

$_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEclEv = comdat any

$_ZNSt8__detail5__modImLm2147483647ELm16807ELm0EEET_S1_ = comdat any

$_ZNSt8__detail4_ModImLm2147483647ELm16807ELm0ELb1ELb1EE6__calcEm = comdat any

@overflows = external dso_local global i32, align 4
@_ZL4SEED = internal constant double 3.180000e+01, align 8
@.str = private unnamed_addr constant [29 x i8] c"input: %A unopt: %i opt: %i\0A\00", align 1
@.str.1 = private unnamed_addr constant [22 x i8] c"%i had no exceptions\0A\00", align 1
@.str.2 = private unnamed_addr constant [27 x i8] c"%i had exceptions in both\0A\00", align 1
@.str.3 = private unnamed_addr constant [32 x i8] c"%i had exceptions only for opt\0A\00", align 1
@.str.4 = private unnamed_addr constant [34 x i8] c"%i had exceptions only for unopt\0A\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @_Z16check_exceptionsv() #0 {
  %1 = alloca double, align 8
  %2 = load i32, i32* @overflows, align 4
  %3 = sitofp i32 %2 to double
  store double %3, double* %1, align 8
  store i32 0, i32* @overflows, align 4
  %4 = load double, double* %1, align 8
  %5 = fptosi double %4 to i32
  ret i32 %5
}

; Function Attrs: noinline norecurse optnone uwtable
define dso_local i32 @main() #1 {
  %1 = alloca i32, align 4
  %2 = alloca %"class.std::linear_congruential_engine", align 8
  %3 = alloca %"class.std::normal_distribution", align 8
  %4 = alloca double, align 8
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca double, align 8
  %11 = alloca i32, align 4
  %12 = alloca double, align 8
  %13 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEC2IKdvEERT_(%"class.std::linear_congruential_engine"* %2, double* dereferenceable(8) @_ZL4SEED)
  call void @_ZNSt19normal_distributionIdEC2Edd(%"class.std::normal_distribution"* %3, double 0.000000e+00, double 5.000000e-01)
  store i32 0, i32* %5, align 4
  store i32 0, i32* %6, align 4
  store i32 0, i32* %7, align 4
  store i32 0, i32* %8, align 4
  store i32 0, i32* %9, align 4
  br label %14

; <label>:14:                                     ; preds = %52, %0
  %15 = load i32, i32* %9, align 4
  %16 = icmp slt i32 %15, 100
  br i1 %16, label %17, label %55

; <label>:17:                                     ; preds = %14
  %18 = call double @_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_(%"class.std::normal_distribution"* %3, %"class.std::linear_congruential_engine"* dereferenceable(8) %2)
  store double %18, double* %4, align 8
  %19 = load double, double* %4, align 8
  %20 = call double @_Z7p_unoptd(double %19)
  store double %20, double* %10, align 8
  %21 = call i32 @_Z16check_exceptionsv()
  store i32 %21, i32* %11, align 4
  %22 = load double, double* %4, align 8
  %23 = call double @_Z5p_optd(double %22)
  store double %23, double* %12, align 8
  %24 = call i32 @_Z16check_exceptionsv()
  store i32 %24, i32* %13, align 4
  %25 = load double, double* %4, align 8
  %26 = load i32, i32* %11, align 4
  %27 = load i32, i32* %13, align 4
  %28 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str, i32 0, i32 0), double %25, i32 %26, i32 %27)
  %29 = load i32, i32* %11, align 4
  %30 = icmp sgt i32 %29, 0
  br i1 %30, label %31, label %41

; <label>:31:                                     ; preds = %17
  %32 = load i32, i32* %13, align 4
  %33 = icmp sgt i32 %32, 0
  br i1 %33, label %34, label %37

; <label>:34:                                     ; preds = %31
  %35 = load i32, i32* %7, align 4
  %36 = add nsw i32 %35, 1
  store i32 %36, i32* %7, align 4
  br label %40

; <label>:37:                                     ; preds = %31
  %38 = load i32, i32* %5, align 4
  %39 = add nsw i32 %38, 1
  store i32 %39, i32* %5, align 4
  br label %40

; <label>:40:                                     ; preds = %37, %34
  br label %51

; <label>:41:                                     ; preds = %17
  %42 = load i32, i32* %13, align 4
  %43 = icmp sgt i32 %42, 0
  br i1 %43, label %44, label %47

; <label>:44:                                     ; preds = %41
  %45 = load i32, i32* %6, align 4
  %46 = add nsw i32 %45, 1
  store i32 %46, i32* %6, align 4
  br label %50

; <label>:47:                                     ; preds = %41
  %48 = load i32, i32* %8, align 4
  %49 = add nsw i32 %48, 1
  store i32 %49, i32* %8, align 4
  br label %50

; <label>:50:                                     ; preds = %47, %44
  br label %51

; <label>:51:                                     ; preds = %50, %40
  br label %52

; <label>:52:                                     ; preds = %51
  %53 = load i32, i32* %9, align 4
  %54 = add nsw i32 %53, 1
  store i32 %54, i32* %9, align 4
  br label %14

; <label>:55:                                     ; preds = %14
  %56 = load i32, i32* %8, align 4
  %57 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str.1, i32 0, i32 0), i32 %56)
  %58 = load i32, i32* %7, align 4
  %59 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.2, i32 0, i32 0), i32 %58)
  %60 = load i32, i32* %6, align 4
  %61 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([32 x i8], [32 x i8]* @.str.3, i32 0, i32 0), i32 %60)
  %62 = load i32, i32* %5, align 4
  %63 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.4, i32 0, i32 0), i32 %62)
  %64 = load i32, i32* %1, align 4
  ret i32 %64
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local void @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEC2IKdvEERT_(%"class.std::linear_congruential_engine"*, double* dereferenceable(8)) unnamed_addr #2 comdat align 2 {
  %3 = alloca %"class.std::linear_congruential_engine"*, align 8
  %4 = alloca double*, align 8
  store %"class.std::linear_congruential_engine"* %0, %"class.std::linear_congruential_engine"** %3, align 8
  store double* %1, double** %4, align 8
  %5 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %3, align 8
  %6 = load double*, double** %4, align 8
  %7 = load double, double* %6, align 8
  %8 = fptoui double %7 to i64
  call void @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE4seedEm(%"class.std::linear_congruential_engine"* %5, i64 %8)
  ret void
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local void @_ZNSt19normal_distributionIdEC2Edd(%"class.std::normal_distribution"*, double, double) unnamed_addr #2 comdat align 2 {
  %4 = alloca %"class.std::normal_distribution"*, align 8
  %5 = alloca double, align 8
  %6 = alloca double, align 8
  store %"class.std::normal_distribution"* %0, %"class.std::normal_distribution"** %4, align 8
  store double %1, double* %5, align 8
  store double %2, double* %6, align 8
  %7 = load %"class.std::normal_distribution"*, %"class.std::normal_distribution"** %4, align 8
  %8 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %7, i32 0, i32 0
  %9 = load double, double* %5, align 8
  %10 = load double, double* %6, align 8
  call void @_ZNSt19normal_distributionIdE10param_typeC2Edd(%"struct.std::normal_distribution<double>::param_type"* %8, double %9, double %10)
  %11 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %7, i32 0, i32 2
  store i8 0, i8* %11, align 8
  ret void
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local double @_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_(%"class.std::normal_distribution"*, %"class.std::linear_congruential_engine"* dereferenceable(8)) #2 comdat align 2 {
  %3 = alloca %"class.std::normal_distribution"*, align 8
  %4 = alloca %"class.std::linear_congruential_engine"*, align 8
  store %"class.std::normal_distribution"* %0, %"class.std::normal_distribution"** %3, align 8
  store %"class.std::linear_congruential_engine"* %1, %"class.std::linear_congruential_engine"** %4, align 8
  %5 = load %"class.std::normal_distribution"*, %"class.std::normal_distribution"** %3, align 8
  %6 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %4, align 8
  %7 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %5, i32 0, i32 0
  %8 = call double @_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_RKNS0_10param_typeE(%"class.std::normal_distribution"* %5, %"class.std::linear_congruential_engine"* dereferenceable(8) %6, %"struct.std::normal_distribution<double>::param_type"* dereferenceable(16) %7)
  ret double %8
}

declare dso_local double @_Z7p_unoptd(double) #3

declare dso_local double @_Z5p_optd(double) #3

declare dso_local i32 @printf(i8*, ...) #3

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local void @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE4seedEm(%"class.std::linear_congruential_engine"*, i64) #2 comdat align 2 {
  %3 = alloca %"class.std::linear_congruential_engine"*, align 8
  %4 = alloca i64, align 8
  store %"class.std::linear_congruential_engine"* %0, %"class.std::linear_congruential_engine"** %3, align 8
  store i64 %1, i64* %4, align 8
  %5 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %3, align 8
  %6 = call i64 @_ZNSt8__detail5__modImLm2147483647ELm1ELm0EEET_S1_(i64 0)
  %7 = icmp eq i64 %6, 0
  br i1 %7, label %8, label %14

; <label>:8:                                      ; preds = %2
  %9 = load i64, i64* %4, align 8
  %10 = call i64 @_ZNSt8__detail5__modImLm2147483647ELm1ELm0EEET_S1_(i64 %9)
  %11 = icmp eq i64 %10, 0
  br i1 %11, label %12, label %14

; <label>:12:                                     ; preds = %8
  %13 = getelementptr inbounds %"class.std::linear_congruential_engine", %"class.std::linear_congruential_engine"* %5, i32 0, i32 0
  store i64 1, i64* %13, align 8
  br label %18

; <label>:14:                                     ; preds = %8, %2
  %15 = load i64, i64* %4, align 8
  %16 = call i64 @_ZNSt8__detail5__modImLm2147483647ELm1ELm0EEET_S1_(i64 %15)
  %17 = getelementptr inbounds %"class.std::linear_congruential_engine", %"class.std::linear_congruential_engine"* %5, i32 0, i32 0
  store i64 %16, i64* %17, align 8
  br label %18

; <label>:18:                                     ; preds = %14, %12
  ret void
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt8__detail5__modImLm2147483647ELm1ELm0EEET_S1_(i64) #2 comdat {
  %2 = alloca i64, align 8
  store i64 %0, i64* %2, align 8
  %3 = load i64, i64* %2, align 8
  %4 = call i64 @_ZNSt8__detail4_ModImLm2147483647ELm1ELm0ELb1ELb1EE6__calcEm(i64 %3)
  ret i64 %4
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt8__detail4_ModImLm2147483647ELm1ELm0ELb1ELb1EE6__calcEm(i64) #0 comdat align 2 {
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  store i64 %0, i64* %2, align 8
  %4 = load i64, i64* %2, align 8
  %5 = mul i64 1, %4
  %6 = add i64 %5, 0
  store i64 %6, i64* %3, align 8
  %7 = load i64, i64* %3, align 8
  %8 = urem i64 %7, 2147483647
  store i64 %8, i64* %3, align 8
  %9 = load i64, i64* %3, align 8
  ret i64 %9
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local void @_ZNSt19normal_distributionIdE10param_typeC2Edd(%"struct.std::normal_distribution<double>::param_type"*, double, double) unnamed_addr #0 comdat align 2 {
  %4 = alloca %"struct.std::normal_distribution<double>::param_type"*, align 8
  %5 = alloca double, align 8
  %6 = alloca double, align 8
  store %"struct.std::normal_distribution<double>::param_type"* %0, %"struct.std::normal_distribution<double>::param_type"** %4, align 8
  store double %1, double* %5, align 8
  store double %2, double* %6, align 8
  %7 = load %"struct.std::normal_distribution<double>::param_type"*, %"struct.std::normal_distribution<double>::param_type"** %4, align 8
  %8 = getelementptr inbounds %"struct.std::normal_distribution<double>::param_type", %"struct.std::normal_distribution<double>::param_type"* %7, i32 0, i32 0
  %9 = load double, double* %5, align 8
  store double %9, double* %8, align 8
  %10 = getelementptr inbounds %"struct.std::normal_distribution<double>::param_type", %"struct.std::normal_distribution<double>::param_type"* %7, i32 0, i32 1
  %11 = load double, double* %6, align 8
  store double %11, double* %10, align 8
  ret void
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local double @_ZNSt19normal_distributionIdEclISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEEEdRT_RKNS0_10param_typeE(%"class.std::normal_distribution"*, %"class.std::linear_congruential_engine"* dereferenceable(8), %"struct.std::normal_distribution<double>::param_type"* dereferenceable(16)) #2 comdat align 2 {
  %4 = alloca %"class.std::normal_distribution"*, align 8
  %5 = alloca %"class.std::linear_congruential_engine"*, align 8
  %6 = alloca %"struct.std::normal_distribution<double>::param_type"*, align 8
  %7 = alloca double, align 8
  %8 = alloca %"struct.std::__detail::_Adaptor", align 8
  %9 = alloca double, align 8
  %10 = alloca double, align 8
  %11 = alloca double, align 8
  %12 = alloca double, align 8
  store %"class.std::normal_distribution"* %0, %"class.std::normal_distribution"** %4, align 8
  store %"class.std::linear_congruential_engine"* %1, %"class.std::linear_congruential_engine"** %5, align 8
  store %"struct.std::normal_distribution<double>::param_type"* %2, %"struct.std::normal_distribution<double>::param_type"** %6, align 8
  %13 = load %"class.std::normal_distribution"*, %"class.std::normal_distribution"** %4, align 8
  %14 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %5, align 8
  call void @_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEC2ERS2_(%"struct.std::__detail::_Adaptor"* %8, %"class.std::linear_congruential_engine"* dereferenceable(8) %14)
  %15 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %13, i32 0, i32 2
  %16 = load i8, i8* %15, align 8
  %17 = trunc i8 %16 to i1
  br i1 %17, label %18, label %22

; <label>:18:                                     ; preds = %3
  %19 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %13, i32 0, i32 2
  store i8 0, i8* %19, align 8
  %20 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %13, i32 0, i32 1
  %21 = load double, double* %20, align 8
  store double %21, double* %7, align 8
  br label %60

; <label>:22:                                     ; preds = %3
  br label %23

; <label>:23:                                     ; preds = %43, %22
  %24 = call double @_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEclEv(%"struct.std::__detail::_Adaptor"* %8)
  %25 = fmul double 2.000000e+00, %24
  %26 = fsub double %25, 1.000000e+00
  store double %26, double* %9, align 8
  %27 = call double @_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEclEv(%"struct.std::__detail::_Adaptor"* %8)
  %28 = fmul double 2.000000e+00, %27
  %29 = fsub double %28, 1.000000e+00
  store double %29, double* %10, align 8
  %30 = load double, double* %9, align 8
  %31 = load double, double* %9, align 8
  %32 = fmul double %30, %31
  %33 = load double, double* %10, align 8
  %34 = load double, double* %10, align 8
  %35 = fmul double %33, %34
  %36 = fadd double %32, %35
  store double %36, double* %11, align 8
  br label %37

; <label>:37:                                     ; preds = %23
  %38 = load double, double* %11, align 8
  %39 = fcmp ogt double %38, 1.000000e+00
  br i1 %39, label %43, label %40

; <label>:40:                                     ; preds = %37
  %41 = load double, double* %11, align 8
  %42 = fcmp oeq double %41, 0.000000e+00
  br label %43

; <label>:43:                                     ; preds = %40, %37
  %44 = phi i1 [ true, %37 ], [ %42, %40 ]
  br i1 %44, label %23, label %45

; <label>:45:                                     ; preds = %43
  %46 = load double, double* %11, align 8
  %47 = call double @log(double %46) #6
  %48 = fmul double -2.000000e+00, %47
  %49 = load double, double* %11, align 8
  %50 = fdiv double %48, %49
  %51 = call double @sqrt(double %50) #6
  store double %51, double* %12, align 8
  %52 = load double, double* %9, align 8
  %53 = load double, double* %12, align 8
  %54 = fmul double %52, %53
  %55 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %13, i32 0, i32 1
  store double %54, double* %55, align 8
  %56 = getelementptr inbounds %"class.std::normal_distribution", %"class.std::normal_distribution"* %13, i32 0, i32 2
  store i8 1, i8* %56, align 8
  %57 = load double, double* %10, align 8
  %58 = load double, double* %12, align 8
  %59 = fmul double %57, %58
  store double %59, double* %7, align 8
  br label %60

; <label>:60:                                     ; preds = %45, %18
  %61 = load double, double* %7, align 8
  %62 = load %"struct.std::normal_distribution<double>::param_type"*, %"struct.std::normal_distribution<double>::param_type"** %6, align 8
  %63 = call double @_ZNKSt19normal_distributionIdE10param_type6stddevEv(%"struct.std::normal_distribution<double>::param_type"* %62)
  %64 = fmul double %61, %63
  %65 = load %"struct.std::normal_distribution<double>::param_type"*, %"struct.std::normal_distribution<double>::param_type"** %6, align 8
  %66 = call double @_ZNKSt19normal_distributionIdE10param_type4meanEv(%"struct.std::normal_distribution<double>::param_type"* %65)
  %67 = fadd double %64, %66
  store double %67, double* %7, align 8
  %68 = load double, double* %7, align 8
  ret double %68
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local void @_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEC2ERS2_(%"struct.std::__detail::_Adaptor"*, %"class.std::linear_congruential_engine"* dereferenceable(8)) unnamed_addr #0 comdat align 2 {
  %3 = alloca %"struct.std::__detail::_Adaptor"*, align 8
  %4 = alloca %"class.std::linear_congruential_engine"*, align 8
  store %"struct.std::__detail::_Adaptor"* %0, %"struct.std::__detail::_Adaptor"** %3, align 8
  store %"class.std::linear_congruential_engine"* %1, %"class.std::linear_congruential_engine"** %4, align 8
  %5 = load %"struct.std::__detail::_Adaptor"*, %"struct.std::__detail::_Adaptor"** %3, align 8
  %6 = getelementptr inbounds %"struct.std::__detail::_Adaptor", %"struct.std::__detail::_Adaptor"* %5, i32 0, i32 0
  %7 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %4, align 8
  store %"class.std::linear_congruential_engine"* %7, %"class.std::linear_congruential_engine"** %6, align 8
  ret void
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local double @_ZNSt8__detail8_AdaptorISt26linear_congruential_engineImLm16807ELm0ELm2147483647EEdEclEv(%"struct.std::__detail::_Adaptor"*) #2 comdat align 2 {
  %2 = alloca %"struct.std::__detail::_Adaptor"*, align 8
  store %"struct.std::__detail::_Adaptor"* %0, %"struct.std::__detail::_Adaptor"** %2, align 8
  %3 = load %"struct.std::__detail::_Adaptor"*, %"struct.std::__detail::_Adaptor"** %2, align 8
  %4 = getelementptr inbounds %"struct.std::__detail::_Adaptor", %"struct.std::__detail::_Adaptor"* %3, i32 0, i32 0
  %5 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %4, align 8
  %6 = call double @_ZSt18generate_canonicalIdLm53ESt26linear_congruential_engineImLm16807ELm0ELm2147483647EEET_RT1_(%"class.std::linear_congruential_engine"* dereferenceable(8) %5)
  ret double %6
}

; Function Attrs: nounwind
declare dso_local double @sqrt(double) #4

; Function Attrs: nounwind
declare dso_local double @log(double) #4

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local double @_ZNKSt19normal_distributionIdE10param_type6stddevEv(%"struct.std::normal_distribution<double>::param_type"*) #0 comdat align 2 {
  %2 = alloca %"struct.std::normal_distribution<double>::param_type"*, align 8
  store %"struct.std::normal_distribution<double>::param_type"* %0, %"struct.std::normal_distribution<double>::param_type"** %2, align 8
  %3 = load %"struct.std::normal_distribution<double>::param_type"*, %"struct.std::normal_distribution<double>::param_type"** %2, align 8
  %4 = getelementptr inbounds %"struct.std::normal_distribution<double>::param_type", %"struct.std::normal_distribution<double>::param_type"* %3, i32 0, i32 1
  %5 = load double, double* %4, align 8
  ret double %5
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local double @_ZNKSt19normal_distributionIdE10param_type4meanEv(%"struct.std::normal_distribution<double>::param_type"*) #0 comdat align 2 {
  %2 = alloca %"struct.std::normal_distribution<double>::param_type"*, align 8
  store %"struct.std::normal_distribution<double>::param_type"* %0, %"struct.std::normal_distribution<double>::param_type"** %2, align 8
  %3 = load %"struct.std::normal_distribution<double>::param_type"*, %"struct.std::normal_distribution<double>::param_type"** %2, align 8
  %4 = getelementptr inbounds %"struct.std::normal_distribution<double>::param_type", %"struct.std::normal_distribution<double>::param_type"* %3, i32 0, i32 0
  %5 = load double, double* %4, align 8
  ret double %5
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local double @_ZSt18generate_canonicalIdLm53ESt26linear_congruential_engineImLm16807ELm0ELm2147483647EEET_RT1_(%"class.std::linear_congruential_engine"* dereferenceable(8)) #2 comdat {
  %2 = alloca %"class.std::linear_congruential_engine"*, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca x86_fp80, align 16
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i64, align 8
  %10 = alloca i64, align 8
  %11 = alloca double, align 8
  %12 = alloca double, align 8
  %13 = alloca double, align 8
  %14 = alloca i64, align 8
  store %"class.std::linear_congruential_engine"* %0, %"class.std::linear_congruential_engine"** %2, align 8
  store i64 53, i64* %4, align 8
  store i64 53, i64* %5, align 8
  %15 = call dereferenceable(8) i64* @_ZSt3minImERKT_S2_S2_(i64* dereferenceable(8) %4, i64* dereferenceable(8) %5)
  %16 = load i64, i64* %15, align 8
  store i64 %16, i64* %3, align 8
  %17 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %2, align 8
  %18 = call i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3maxEv()
  %19 = uitofp i64 %18 to x86_fp80
  %20 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %2, align 8
  %21 = call i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3minEv()
  %22 = uitofp i64 %21 to x86_fp80
  %23 = fsub x86_fp80 %19, %22
  %24 = fadd x86_fp80 %23, 0xK3FFF8000000000000000
  store x86_fp80 %24, x86_fp80* %6, align 16
  %25 = load x86_fp80, x86_fp80* %6, align 16
  %26 = call x86_fp80 @_ZSt3loge(x86_fp80 %25)
  %27 = call x86_fp80 @_ZSt3loge(x86_fp80 0xK40008000000000000000)
  %28 = fdiv x86_fp80 %26, %27
  %29 = fptoui x86_fp80 %28 to i64
  store i64 %29, i64* %7, align 8
  store i64 1, i64* %9, align 8
  %30 = load i64, i64* %7, align 8
  %31 = add i64 53, %30
  %32 = sub i64 %31, 1
  %33 = load i64, i64* %7, align 8
  %34 = udiv i64 %32, %33
  store i64 %34, i64* %10, align 8
  %35 = call dereferenceable(8) i64* @_ZSt3maxImERKT_S2_S2_(i64* dereferenceable(8) %9, i64* dereferenceable(8) %10)
  %36 = load i64, i64* %35, align 8
  store i64 %36, i64* %8, align 8
  store double 0.000000e+00, double* %12, align 8
  store double 1.000000e+00, double* %13, align 8
  %37 = load i64, i64* %8, align 8
  store i64 %37, i64* %14, align 8
  br label %38

; <label>:38:                                     ; preds = %57, %1
  %39 = load i64, i64* %14, align 8
  %40 = icmp ne i64 %39, 0
  br i1 %40, label %41, label %60

; <label>:41:                                     ; preds = %38
  %42 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %2, align 8
  %43 = call i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEclEv(%"class.std::linear_congruential_engine"* %42)
  %44 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %2, align 8
  %45 = call i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3minEv()
  %46 = sub i64 %43, %45
  %47 = uitofp i64 %46 to double
  %48 = load double, double* %13, align 8
  %49 = fmul double %47, %48
  %50 = load double, double* %12, align 8
  %51 = fadd double %50, %49
  store double %51, double* %12, align 8
  %52 = load x86_fp80, x86_fp80* %6, align 16
  %53 = load double, double* %13, align 8
  %54 = fpext double %53 to x86_fp80
  %55 = fmul x86_fp80 %54, %52
  %56 = fptrunc x86_fp80 %55 to double
  store double %56, double* %13, align 8
  br label %57

; <label>:57:                                     ; preds = %41
  %58 = load i64, i64* %14, align 8
  %59 = add i64 %58, -1
  store i64 %59, i64* %14, align 8
  br label %38

; <label>:60:                                     ; preds = %38
  %61 = load double, double* %12, align 8
  %62 = load double, double* %13, align 8
  %63 = fdiv double %61, %62
  store double %63, double* %11, align 8
  %64 = load double, double* %11, align 8
  %65 = fcmp oge double %64, 1.000000e+00
  br i1 %65, label %66, label %68

; <label>:66:                                     ; preds = %60
  %67 = call double @nextafter(double 1.000000e+00, double 0.000000e+00) #7
  store double %67, double* %11, align 8
  br label %68

; <label>:68:                                     ; preds = %66, %60
  %69 = load double, double* %11, align 8
  ret double %69
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local dereferenceable(8) i64* @_ZSt3minImERKT_S2_S2_(i64* dereferenceable(8), i64* dereferenceable(8)) #0 comdat {
  %3 = alloca i64*, align 8
  %4 = alloca i64*, align 8
  %5 = alloca i64*, align 8
  store i64* %0, i64** %4, align 8
  store i64* %1, i64** %5, align 8
  %6 = load i64*, i64** %5, align 8
  %7 = load i64, i64* %6, align 8
  %8 = load i64*, i64** %4, align 8
  %9 = load i64, i64* %8, align 8
  %10 = icmp ult i64 %7, %9
  br i1 %10, label %11, label %13

; <label>:11:                                     ; preds = %2
  %12 = load i64*, i64** %5, align 8
  store i64* %12, i64** %3, align 8
  br label %15

; <label>:13:                                     ; preds = %2
  %14 = load i64*, i64** %4, align 8
  store i64* %14, i64** %3, align 8
  br label %15

; <label>:15:                                     ; preds = %13, %11
  %16 = load i64*, i64** %3, align 8
  ret i64* %16
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3maxEv() #0 comdat align 2 {
  ret i64 2147483646
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EE3minEv() #0 comdat align 2 {
  ret i64 1
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local x86_fp80 @_ZSt3loge(x86_fp80) #0 comdat {
  %2 = alloca x86_fp80, align 16
  store x86_fp80 %0, x86_fp80* %2, align 16
  %3 = load x86_fp80, x86_fp80* %2, align 16
  %4 = call x86_fp80 @logl(x86_fp80 %3) #6
  ret x86_fp80 %4
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local dereferenceable(8) i64* @_ZSt3maxImERKT_S2_S2_(i64* dereferenceable(8), i64* dereferenceable(8)) #0 comdat {
  %3 = alloca i64*, align 8
  %4 = alloca i64*, align 8
  %5 = alloca i64*, align 8
  store i64* %0, i64** %4, align 8
  store i64* %1, i64** %5, align 8
  %6 = load i64*, i64** %4, align 8
  %7 = load i64, i64* %6, align 8
  %8 = load i64*, i64** %5, align 8
  %9 = load i64, i64* %8, align 8
  %10 = icmp ult i64 %7, %9
  br i1 %10, label %11, label %13

; <label>:11:                                     ; preds = %2
  %12 = load i64*, i64** %5, align 8
  store i64* %12, i64** %3, align 8
  br label %15

; <label>:13:                                     ; preds = %2
  %14 = load i64*, i64** %4, align 8
  store i64* %14, i64** %3, align 8
  br label %15

; <label>:15:                                     ; preds = %13, %11
  %16 = load i64*, i64** %3, align 8
  ret i64* %16
}

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt26linear_congruential_engineImLm16807ELm0ELm2147483647EEclEv(%"class.std::linear_congruential_engine"*) #2 comdat align 2 {
  %2 = alloca %"class.std::linear_congruential_engine"*, align 8
  store %"class.std::linear_congruential_engine"* %0, %"class.std::linear_congruential_engine"** %2, align 8
  %3 = load %"class.std::linear_congruential_engine"*, %"class.std::linear_congruential_engine"** %2, align 8
  %4 = getelementptr inbounds %"class.std::linear_congruential_engine", %"class.std::linear_congruential_engine"* %3, i32 0, i32 0
  %5 = load i64, i64* %4, align 8
  %6 = call i64 @_ZNSt8__detail5__modImLm2147483647ELm16807ELm0EEET_S1_(i64 %5)
  %7 = getelementptr inbounds %"class.std::linear_congruential_engine", %"class.std::linear_congruential_engine"* %3, i32 0, i32 0
  store i64 %6, i64* %7, align 8
  %8 = getelementptr inbounds %"class.std::linear_congruential_engine", %"class.std::linear_congruential_engine"* %3, i32 0, i32 0
  %9 = load i64, i64* %8, align 8
  ret i64 %9
}

; Function Attrs: nounwind readnone
declare dso_local double @nextafter(double, double) #5

; Function Attrs: nounwind
declare dso_local x86_fp80 @logl(x86_fp80) #4

; Function Attrs: noinline optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt8__detail5__modImLm2147483647ELm16807ELm0EEET_S1_(i64) #2 comdat {
  %2 = alloca i64, align 8
  store i64 %0, i64* %2, align 8
  %3 = load i64, i64* %2, align 8
  %4 = call i64 @_ZNSt8__detail4_ModImLm2147483647ELm16807ELm0ELb1ELb1EE6__calcEm(i64 %3)
  ret i64 %4
}

; Function Attrs: noinline nounwind optnone uwtable
define linkonce_odr dso_local i64 @_ZNSt8__detail4_ModImLm2147483647ELm16807ELm0ELb1ELb1EE6__calcEm(i64) #0 comdat align 2 {
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  store i64 %0, i64* %2, align 8
  %4 = load i64, i64* %2, align 8
  %5 = mul i64 16807, %4
  %6 = add i64 %5, 0
  store i64 %6, i64* %3, align 8
  %7 = load i64, i64* %3, align 8
  %8 = urem i64 %7, 2147483647
  store i64 %8, i64* %3, align 8
  %9 = load i64, i64* %3, align 8
  ret i64 %9
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline norecurse optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind readnone "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind }
attributes #7 = { nounwind readnone }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 8.0.1-svn369350-1~exp1~20190820123616.77 (branches/release_80)"}
