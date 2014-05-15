type 'a context = (Term.var * 'a) list

val take_subcontext : 'a context -> Term.t -> 'a context * 'a context
val split_context : 'a context -> Term.t -> Term.t -> 'a context * 'a context

exception Typing_error of Term.t option * string                  

(* Principal types. *)
(* raises Typing_error, unifies types as a side effect *)
val principal_typeW: Basetype.t context -> Type.t context -> Term.t -> Basetype.t

(* raises Typing_error, unifies types as a side effect *)
val principal_type: Basetype.t context -> Type.t context -> Term.t -> Type.t
