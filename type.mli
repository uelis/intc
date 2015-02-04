(** Representation of interactive types *)

open Core.Std

type 'a sgn =
  | Base of Basetype.t
  | Tensor of 'a * 'a
  | FunV of Basetype.t * 'a
  | FunI of Basetype.t * 'a * 'a
with sexp

include Uftype.S with type 'a Sgn.t = 'a sgn

(** Substitution of types for types and base types for base types. *)
val full_subst: t -> (t -> t) -> (Basetype.t -> Basetype.t) -> t

(** Apply the given function to all index types in the given
    type. Index types are all the types [a] in [FunI(a, _, _)]. *)
val map_index_types: t -> (Basetype.t -> Basetype.t) -> t

(* Given an interactive  type X, returns the pair (X^-, X^+). *)
val question_answer_pair: t -> Basetype.t * Basetype.t
