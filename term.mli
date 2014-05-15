(** Source terms *)

type var = string

val unusable_var : var

module Location : sig
  type pos = { column: int; line: int} 
  type loc = {start_pos: pos; end_pos: pos} 
  type t = loc option
  val none: t
end

type value_const =
  | Cundef of Basetype.t
  | Cintconst of int

type op_const =
  | Cprint of string
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintslt
  | Cintprint
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t

(* TODO: dokumentiere typannotationen (bei Box ist es der Inhalt) 
- Konstruktoren BindW und LetW haben inkonsistente Typannotationen                                     
*)
type t = { 
  desc: t_desc;      
  loc: Location.t 
} and t_desc =
  | Var of var
  | ValW of value_const 
  | ConstW of op_const 
  | UnitW 
  | PairW of (t * Basetype.t) * (t * Basetype.t)
  | FstW of t * Basetype.t * Basetype.t
  | SndW of t * Basetype.t * Basetype.t
  | InW of (Basetype.Data.id * int * t) * Basetype.t
  | BindW of (t * Basetype.t) * (var * t)
  | App of t * Type.t * t
  | Box of t * Basetype.t
  | Unbox of t * Basetype.t
  | Case of Basetype.Data.id * (Basetype.t list) * t * ((var * t) list)
  | Select of Basetype.Data.id * (Basetype.t list) * t * int
  | LambdaW of (var * Basetype.t) * t
  | LambdaU of (var * Basetype.t * Type.t) * t
  | CopyU of t * (var * var * t)
  | HackU of Type.t * t
  | ExternalU of (string * Type.t (* type schema *)) * Type.t
  | TypeAnnot of t * Type.t
                   
(* The following functions fill in fresh type variables for
   annotations. *)
val mkTerm : t_desc -> t
val mkVar : var -> t
val mkConstW : op_const -> t
val mkUnitW : t
val mkPairW : t -> t -> t
val mkFstW : t -> t
val mkSndW : t -> t
val mkInW : Basetype.Data.id -> int -> t -> t
val mkInlW : t -> t
val mkInrW : t -> t
val mkCase : Basetype.Data.id -> t -> (var * t) list -> t
val mkApp : t -> t -> t
val mkBox : t -> t
val mkUnbox : t -> t
val mkLambdaW : (var * Basetype.t) * t -> t
val mkBindW : t -> (var * t) -> t
val mkLambdaU : (var * Basetype.t * Type.t) * t -> t
val mkCopyU : t -> (var * var) * t -> t
val mkHackU : Type.t -> t -> t
val mkTypeAnnot : t -> Type.t -> t

val let_tupleW : var -> (var list) * t -> t

val is_value: t -> bool
val is_pure: t -> bool

(** Free variables *)
val free_vars : t -> var list 
(** All variables, free and bound *)
val all_vars : t -> var list
val rename_vars : (var -> var) -> t -> t 
val variant_var : var -> var
val variant_var_avoid: var -> var list -> var
val variant : t -> t

(** Renames all variables with new names drawn from 
    the given name-supply. *)
val variant_with_name_supply : (unit -> var) -> t -> t 

(** Head substitution.
    head_subst s x t substitues s for the head occurrence of x,
    if one exists. It returns None if t does not contain x. *)
val head_subst: t -> var -> t -> t option
(* TODO: (subst "<x,x>" "x" "x") should be incorrect *)
val subst: t -> var -> t -> t

val freshen_type_vars : t -> t
