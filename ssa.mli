(** Progams in functional SSA form *)

open Core.Std

(** SSA values and terms *)
type value =
  | Var of Ast.var
  | Unit
  | Pair of value * value
  | In of (Basetype.Data.id * int * value) * Basetype.t
  | Fst of value * Basetype.t * Basetype.t
  | Snd of value * Basetype.t * Basetype.t
  | Select of value * (Basetype.Data.id * Basetype.t list) * int
  | Undef of Basetype.t
  | IntConst of int
type term =
  | Val of value
  | Const of Ast.op_const * value

(** Substition of values in values *)
val subst_value: (Ast.var -> value) -> value -> value

(** Substition of values in terms *)
val subst_term: (Ast.var -> value) -> term -> term

(** Straight-line programs are given by let bindings *)
type let_binding =
  | Let of (Ast.var * Basetype.t) * term

(** A block is a list of let bindings in reverse order. *)
type let_bindings = let_binding list

(** Programs consist of a list of blocks, which each defines a label.*)
type label = {
  name: int;
  message_type: Basetype.t
}

(** Program blocks *)
type block =
  | Unreachable of label
  | Direct of label * Ast.var * let_bindings * value * label
  | Branch of label * Ast.var * let_bindings *
              (Basetype.Data.id * Basetype.t list * value *
               (Ast.var * value * label) list)
  | Return of label * Ast.var * let_bindings * value * Basetype.t

(** Return the label defined by a block *)
val label_of_block: block -> label

(** Return the jump targets of a block *)
val targets_of_block: block -> label list

(** A program in SSA form. *)
type t = private {
  func_name : string;
  entry_label: label;
  blocks : block list;
  return_type: Basetype.t;
}

(** Construct a SSA program from its part.
    This function verifies the representation invariants and
    verifies the program for type correctness, if assertions
    are enabled. *)
val make:
  func_name:string ->
  entry_label:label ->
  blocks: block list ->
  return_type: Basetype.t ->
  t

val circuit_to_ssa: string -> Circuit.t -> t

val fprint_value : Out_channel.t -> value -> unit
val fprint_term : Out_channel.t -> term -> unit
val fprint_letbndgs : Out_channel.t -> let_bindings -> unit
val fprint_block : Out_channel.t -> block -> unit
val fprint_func : Out_channel.t -> t -> unit
