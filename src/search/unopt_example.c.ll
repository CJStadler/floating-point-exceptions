; ModuleID = 'unopt_example.c.ll'
source_filename = "example.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @run(double) #0 !dbg !7 {
  %2 = alloca double, align 8
  store double %0, double* %2, align 8
  call void @llvm.dbg.declare(metadata double* %2, metadata !12, metadata !DIExpression()), !dbg !13
  %3 = load double, double* %2, align 8, !dbg !14
  %4 = fmul fast double %3, 2.000000e+00, !dbg !14
  call void @check_for_exception(i32 6), !dbg !14
  store double %4, double* %2, align 8, !dbg !14
  %5 = load double, double* %2, align 8, !dbg !15
  %6 = fmul fast double %5, 2.000000e+00, !dbg !15
  call void @check_for_exception(i32 7), !dbg !15
  store double %6, double* %2, align 8, !dbg !15
  %7 = load double, double* %2, align 8, !dbg !16
  %8 = fptosi double %7 to i32, !dbg !16
  ret i32 %8, !dbg !17
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

declare void @check_for_exception(i32)

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="true" "no-jump-tables"="false" "no-nans-fp-math"="true" "no-signed-zeros-fp-math"="true" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="true" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 8.0.1-svn369350-1~exp1~20190820123616.77 (branches/release_80)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: None)
!1 = !DIFile(filename: "example.c", directory: "/home/chris/workspace/numeric-instability/src/search")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{!"clang version 8.0.1-svn369350-1~exp1~20190820123616.77 (branches/release_80)"}
!7 = distinct !DISubprogram(name: "run", scope: !1, file: !1, line: 5, type: !8, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DISubroutineType(types: !9)
!9 = !{!10, !11}
!10 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!11 = !DIBasicType(name: "double", size: 64, encoding: DW_ATE_float)
!12 = !DILocalVariable(name: "x", arg: 1, scope: !7, file: !1, line: 5, type: !11)
!13 = !DILocation(line: 5, column: 16, scope: !7)
!14 = !DILocation(line: 6, column: 5, scope: !7)
!15 = !DILocation(line: 7, column: 5, scope: !7)
!16 = !DILocation(line: 8, column: 10, scope: !7)
!17 = !DILocation(line: 8, column: 3, scope: !7)
