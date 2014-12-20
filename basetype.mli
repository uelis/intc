(** Representation of low-level types.

    This modules represents the first-order value types that
    are used in the low-level language.

    {v A,B ::= 'a | 0 | int | unit | A x B | box<A> | data<A1,...,A_n>  v}

    The type [box<A>] is intended to contain boxed values of type [A].

    Algebraic data types may be recursive, but each recursive occurrence
    must appear boxed.
*)

open Core.Std

(** The representation of types uses a union find data
    structure that makes unification easy.
    I learned about this representation of types
    from the following article (Section 1.4):
    Didier Remy. Using, Understanding, and Unraveling
    The OCaml Language. LNCS 2395. Springer-Verlag 2002
    http://pauillac.inria.fr/~remy/cours/appsem/
*)

type t = {
  mutable desc : desc;
  mutable mark : int;
  id : int (* unique id *)
}
and desc =
  | Link of t
  | Var
  | IntB
  | ZeroB
  | UnitB
  | BoxB of t
  | ArrayB of t
  | PairB of t * t
  | DataB of string * t list

val sexp_of_t: t -> Sexplib.Sexp.t
val t_of_sexp: Sexplib.Sexp.t -> t


include Types.Repr
  with type t := t with type desc := desc

(** Representation of algebraic data types.
*)
module Data:
sig
  (** Data type names, e.g. "list" *)
  type id = string

  (** Name of the n-ary sum type *)
  val sumid : int -> id

  (** Name of the bool type *)
  val boolid : id

  (** Generate a new data type name.
      This is useful for generating types programmatically. *)
  val fresh_id : string -> id

  (** Number of type parameters of a data type.
      For example, pair<'a,'b> has two parameters *)
  val params : id -> int

  (** Number of constructors *)
  val constructor_count : id -> int

  (** Names of the constructors *)
  val constructor_names : id -> string list

  (** Given a name of a data type and a list of its type parameters,
      returns the types of the constructors of the type.
      The argument list must have the same length as the value
      returned by [params]. *)
  val constructor_types : id -> t list -> t list

  (** The data type is recursive. *)
  val is_recursive: id -> bool

  (** Non-discriminated unions are possible.*)
  val is_discriminated: id -> bool

  (** Look up a constructor by name. *)
  val find_constructor: string -> id * int

  (** Add a new data type, initially with no constructors. *)
  val make : id -> nparams:int -> discriminated:bool -> unit

  (** Add a constructor.
      The call [add_constructor id name params a] adds a
      constructor of type "[name: a -> id<params>]", where
      [id<params>] means the instantiation of the data type
      at the parameters [params].

      To add a constructor [cons: 'a -> list<'a>], one would
      call [add_constructor "list" "cons" ['a] 'a].

      Preconditions:
      - No constructor called [name] is already defined.
      - [params] is a list of type variables.
      - The free type variables in [a] are contained in [params].
  *)
  val add_constructor : id -> string -> t list -> t -> unit
end

val newtyvar: unit -> t

(** Returns the list of free type variables in their order of
    appearance in the term, including duplicates.
*)
val free_vars: t -> t list

(** Substitution.
    The result of [subst f t] is the term obtained by
    replacing each variable [alpha] in [t] by [f alpha].
*)
val subst: (t -> t) -> t -> t

(** Replace all type variables by fresh variables *)
val freshen: t -> t

(** Freshen a list of types. If a variable alpha appears in more
    than one type in the input list, then any occurrence will be
    replaced with the same new variabe.
*)
val freshen_list: t list -> t list
