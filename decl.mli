(** Declarations in an input file *)

(** Currently there is just a single declaration for interaction terms *)
type t =
  | TermDecl of Ident.t * Ast.t

(** Exception to use when reading an illformed declaration.
    The argments are error message, line and column. *)
exception Illformed_decl of string * int * int

(** Expand left-hand side of declaration in term.
    Each occurrencd of the left-hand side of the given
    declaration is replaced with an instance of its
    right-hand side with _fresh type variables_.
 *)
val expand_in_term: t -> Ast.t -> Ast.t

(** Expand declaration in right-hand side of declaration. *)
val expand: t -> t -> t

(** Expand all declarations repeatedly, so that no occurrence of
    a left-hand side remains. *)
val expand_all: t list -> t list
