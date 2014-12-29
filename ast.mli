(** Source terms *)

(** Variables are string *)
type var = string

(** A variable that cannot appear from parsing a source term.
    It is useful in constructing terms to be sure that there
    are no name collisions. *)
val unusable_var : var

(** Location of term in the source file *)
module Location : sig
  type pos = { column: int; line: int}
  type loc = {start_pos: pos; end_pos: pos}
  type t = loc option
  val none: t
end

(** Value constants *)
type value_const =
  | Cundef of Basetype.t
  | Cintconst of int

(** Primitive operations *)
type op_const =
  | Cprint of string
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintlt
  | Cintslt
  | Cintshl
  | Cintshr
  | Cintsar
  | Cintand
  | Cintor
  | Cintxor
  | Cintprint
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Carrayalloc of Basetype.t
  | Carrayfree of Basetype.t
  | Carrayget of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t
  | Cencode of Basetype.t * Basetype.t
  | Cdecode of Basetype.t * Basetype.t

(** The type of terms is a single type to represent both value terms
    and interaction terms. Eventually, we are interested only in terms
    corresponding to the following grammar.
    {|
     v,w ::= variable | value constant
           | () | (v, w) | fst(v) | snd(v)
           | Cons_i(v) | Select_i(v)
     s,t ::= variable | constant | return v | let x = s in t
           | fn x -> t | \ x -> t | s t | s v
           | case v of Cons_1(x) -> t1 ...
           | copy s as x1, x2 in t
           | (s # t) | let (x # y) = s in t
           | direct(s : a)
           | external(f : a)
           | (s : a)
    |}
    The type of terms here can represent more terms, e.g. it allows interaction terms
    also in values. The type checker will later check that they correspond to the
    above grammar and produce typed terms that are separated in values and interactive
    terms, see typedterm.mli. *)
type t = {
  desc: t_desc;
  loc: Location.t
} and t_desc =
  | Var of var
  (* value terms *)
  | ConstV of value_const
  | UnitV
  | PairV of t * t
  | FstV of t
  | SndV of t
  | InV of (Basetype.Data.id * int * t)
  | SelectV of Basetype.Data.id * (Basetype.t list) * t * int
  (* interaction terms *)
  | Const of op_const
  | Return of t
  | Bind of t * (var * t)
  | Fn of (var * Basetype.t) * t
  | Fun of (var * Basetype.t * Type.t) * t
  | App of t * t
  | Case of Basetype.Data.id * t * ((var * t) list)
  | Copy of t * (var list * t)
  | Pair of t * t
  | LetPair of t * (var * var * t)
  | Direct of Type.t * t
  | TypeAnnot of t * Type.t

(* The following functions fill in fresh type variables for
   annotations. *)
val mkTerm : t_desc -> t
val mkVar : var -> t
val mkConstV : value_const -> t
val mkConst : op_const -> t
val mkUnitV : t
val mkPairV : t -> t -> t
val mkFstV : t -> t
val mkSndV : t -> t
val mkInV : Basetype.Data.id -> int -> t -> t
val mkInlV : t -> t
val mkInrV : t -> t
val mkCase : Basetype.Data.id -> t -> (var * t) list -> t
val mkApp : t -> t -> t
val mkFn : (var * Basetype.t) * t -> t
val mkReturn : t -> t
val mkBind : t -> (var * t) -> t
val mkFun : (var * Basetype.t * Type.t) * t -> t
val mkCopy : t -> (var list) * t -> t
val mkDirect : Type.t -> t -> t
val mkTypeAnnot : t -> Type.t -> t
val mkBox : t -> t
val mkUnbox : t -> t

(** Check if a term conforms to the grammar of value terms. *)
val is_value: t -> bool

(** Free variables *)
val free_vars : t -> var list

(** All variables, free and bound *)
val all_vars : t -> var list

(** Rename variables using given function. *)
val rename_vars : (var -> var) -> t -> t

(** Return a variant of the variable by mapping ["x"] to ["x'"].
    The optional argument allows one to specify a list of names to
    avoid in the result. *)
val variant_var : var -> var

(** Return a variant of the variable by mapping ["x"] to ["x'"]
    repeatedly (at least once), so long until the result does not
    appear in the given list of variables to avoid.*)
val variant_var_avoid: var -> var list -> var

(** Compute variant of the term.
    Equivalent to [rename_vars variant_var]. *)
val variant : t -> t

(** Renames all variables with new names drawn from
    the given name-supply. *)
val variant_with_name_supply : (unit -> var) -> t -> t

(** Head substitution.
    [head_subst s x t] substitues [s] for the head occurrence of [x],
    if one exists. It returns [None] if [t] does not contain [x]. *)
val head_subst: t -> var -> t -> t option

(** Capture avoiding substitution.
    [subst s x t] substitues [s] for [x] in [t]. *)
val subst: t -> var -> t -> t

(** Rename type variables in type annotations with fresh type variables. *)
val freshen_type_vars : t -> t
