(** LLVM code generation from SSA programs. *)

val llvm_compile: Ssa.t -> Llvm.llmodule

