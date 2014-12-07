open Core.Std

(* The representation of types uses a union find data
 * structure that makes unification easy. 
 * I learned about this representation of types
 * from the following article (Section 1.4):
 *   Didier Rémy. Using, Understanding, and Unraveling
 *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
 *   http://pauillac.inria.fr/~remy/cours/appsem/
 *)

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

val subst: (t -> t) -> (Basetype.t -> Basetype.t) -> t -> t

val freshen: t -> t
val map_index_types: t -> (Basetype.t -> Basetype.t) -> t

(* Given upper class type X, returns the pair (X^-, X^+). *)
val question_answer_pair: t -> Basetype.t * Basetype.t

