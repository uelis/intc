type label = { 
  name: int; 
  message_type: Basetype.t
}

type value =
  | Var of Term.var
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
  | Alloc of Basetype.t
  | Free of value * Basetype.t
  | Load of value * Basetype.t
  | Store of value * value * Basetype.t
  | Const of Term.op_const * value 

val subst_value: (Term.var -> value) -> value -> value
val subst_term: (Term.var -> value) -> term -> term

type let_binding =
  | Let of (Term.var * Basetype.t) * term
type let_bindings = let_binding list 

type block = 
    Unreachable of label
  | Direct of label * Term.var * let_bindings * value * label
  | InDirect of label * Term.var * let_bindings * value * (label list)
  | Branch of label * Term.var * let_bindings * 
              (Basetype.Data.id * Basetype.t list * value * 
               (Term.var * value * label) list)
  | Return of label * Term.var * let_bindings * value * Basetype.t

val label_of_block: block -> label
val targets_of_block: block -> label list

(** Invariant: Any block [b] in the list [blocks] must 
    be reachable from the entry label over blocks appearing
    before it in the list of blocks. 
*)
type t = private {
  func_name : string;
  entry_label: label;
  blocks : block list;
  return_type: Basetype.t;
}

val make: 
  func_name:string -> 
  entry_label:label -> 
  blocks: block list ->
  return_type: Basetype.t -> 
  t

val circuit_to_ssa: string -> Circuit.t -> t                                      

val string_of_value : value -> string
val string_of_term : term -> string
val string_of_letbndgs : let_bindings -> string
val string_of_block : block -> string
val string_of_func : t -> string
