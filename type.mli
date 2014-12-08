(** Representation of interactive types *)

open Core.Std

type t = 
   { mutable desc : desc; 
     mutable mark : int;
     id : int
   }
and desc = 
  | Link of t
  | Var
  | Base of Basetype.t
  | Tensor of t * t
  | FunW of Basetype.t * t
  | FunU of Basetype.t * t * t

include Types.Repr 
  with type t := t with type desc := desc

(** Substitution of types for types and base types for base types. *)
val subst: (t -> t) -> (Basetype.t -> Basetype.t) -> t -> t

(** Freshen all type variables, both for interactive types and 
    for base types. *)
val freshen: t -> t

(** Apply the given function to all index types in the given
    type. Index types are all the types [a] in [FunU(a, _, _)]. *)
val map_index_types: t -> (Basetype.t -> Basetype.t) -> t

(* Given an interactive  type X, returns the pair (X^-, X^+). *)
val question_answer_pair: t -> Basetype.t * Basetype.t
