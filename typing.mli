(** Type inference *)

(** Type contexts *)
type 'a context = (Ast.var * 'a) list

exception Typing_error of Ast.t option * string

(** Type check a value term and produce a typed value.
    Type variables appearing in annotations are unified as a side effect.
    Type error is indicated by raising [Typing_error] with the offending
    term and reason. *)
val check_value:
  Basetype.t context -> Ast.t -> Typedterm.value

(** Type check an interactive term and produce a typed term.
    Index types are _not considered_, i.e. only Hindley-Milner style
    type inference is performed and all index types are left as type
    variables. Index types annotations are inferred in the translation to
    circuits.

    Type variables are unified as a side effect.
    Type error is indicated by raising [Typing_error] with the offending
    term and reason. *)
val check_term:
  Basetype.t context -> Type.t context -> Ast.t -> Typedterm.t
