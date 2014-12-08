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
  | Cintslt
  | Cintprint
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
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
    above grammar. It seems to be better to do it this way, as this simplifies the
    parser and its error reporting. *)
type t = { 
  desc: t_desc;      
  loc: Location.t 
} and t_desc =
  | Var of var
  (* value terms *)
  | ConstV of value_const
  | UnitV 
  | PairV of (t * Basetype.t) * (t * Basetype.t)
  | FstV of t * Basetype.t * Basetype.t
  | SndV of t * Basetype.t * Basetype.t
  | InV of (Basetype.Data.id * int * t) * Basetype.t
  | Select of Basetype.Data.id * (Basetype.t list) * t * int
  (* interaction terms *)
  | Const of op_const
  | Return of t * Basetype.t
  | Bind of (t * Basetype.t) * (var * t)
  | Fn of (var * Basetype.t) * t
  | Fun of (var * Basetype.t * Type.t) * t
  | App of t * Type.t * t
  | Case of Basetype.Data.id * (Basetype.t list) * t * ((var * t) list)
  | CopyU of t * (var * var * t)
  | Pair of t * t
  | LetPair of t* ((var * Type.t) * (var * Type.t) * t)
  | HackU of Type.t * t
  | ExternalU of (string * Type.t (* type schema *)) * Type.t
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
val mkCopyU : t -> (var * var) * t -> t
val mkHackU : Type.t -> t -> t
val mkTypeAnnot : t -> Type.t -> t
val mkBox : t -> t
val mkUnbox : t -> t

val mkBindList : var -> (var list) * t -> t

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
