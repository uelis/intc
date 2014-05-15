; ModuleID = 'salloc.c'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i64:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@stack = global [10000000 x i8] zeroinitializer, align 16
@top = global i64 9999999, align 4

define i8* @salloc(i64 %size) nounwind uwtable {
  %1 = alloca i64, align 4
  store i64 %size, i64* %1, align 4
  %2 = load i64* %1, align 4
  %3 = load i64* @top, align 4
  %4 = sub nsw i64 %3, %2
  store i64 %4, i64* @top, align 4
  %5 = load i64* @top, align 4
  %6 = add i64 %5, 0
  %7 = getelementptr inbounds [10000000 x i8]* @stack, i64 0, i64 %6
  ret i8* %7
}

define i8* @spop(i64 %size) nounwind uwtable {
  %1 = alloca i64, align 4
  %addr = alloca i8*, align 8
  store i64 %size, i64* %1, align 4
  %2 = load i64* @top, align 4
  %3 = add i64 %2, 0
  %4 = getelementptr inbounds [10000000 x i8]* @stack, i64 0, i64 %3
  store i8* %4, i8** %addr, align 8
  %5 = load i64* %1, align 4
  %6 = load i64* @top, align 4
  %7 = add nsw i64 %6, %5
  store i64 %7, i64* @top, align 4
  %8 = load i8** %addr, align 8
  ret i8* %8
}
