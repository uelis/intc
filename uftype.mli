(** Union-find representation of types for any given signature. *)
open Core.Std

(** Exception raised in unification if the root constructors of the 
    unified types do not match. *)
exception Constructor_mismatch
  
(** Exception raised in unification if the unified type would be 
    cyclic. *)
exception Cyclic_type

(** Signature of type constructors *)
module type Typesgn = sig
  
  (** Constructors over values of type ['a].
      For a type with nat and functions, the signature would be
      [type 'a t = Nat | Fun of 'a * 'a].  *)
  type 'a t with sexp
  
  val map: ('a -> 'b) -> 'a t -> 'b t
                                   
  val children: 'a t -> 'a list

  val equals: 'a t -> 'a t -> equals:('a -> 'a -> bool) -> bool

  (** Unification of consructors.
      May raise the exceptions [Constructor_mismatch] or [Cyclic_type]. *)
  val unify_exn: 'a t -> 'a t -> unify:('a -> 'a -> unit) -> unit
end

(** Union-find representation of types *)
module type S = sig
  type t with sexp

  (** Signature of type constructors. *)
  module Sgn: Typesgn

  (** A variable or type constructor from the signature. *)
  type 'a var_or_sgn =
    | Var
    | Sgn of 'a Sgn.t

  (** Unique representation id of each type.
      This id will be modified by unification.
  *)
  val repr_id : t -> int

  (** Construct a new type variable. *)
  val newvar : unit -> t

  (** Construct a type from a given constructor application. *)
  val newty : t Sgn.t -> t
  
  (** Type variables in type. *)
  val free_vars: t -> t list

  (** Rename each type variable in the given type with a fresh name. *)
  val freshen: t -> t

  (** Rename each type variable in the given types with a fresh name.
      If a variable appears more than once in the list, then it will be
      renamed to the same fresh name. *)
  val freshen_list: t list -> t list

  (** Delete the given type and replace it by the second type. *)
  val replace_by: t -> t -> unit

  (** Substitution. The call [subst a f] applies [f] to all variables in [a]. *)
  val subst: t -> (t -> t) -> t

  (** [case x] returns whether the root of the syntax tree represented by [x]
      is a variable or signature constructor. *)
  val case : t -> t var_or_sgn

  (** Equality of types. Checks if two types repesent the same syntax tree. *)
  val equals : t -> t -> bool

  (** Unification of types.
      May raise the exceptions [Constructor_mismatch] or [Cyclic_type].*)
  val unify_exn : t -> t -> unit
    
  (** Finds the points where a dfs walk in the syntax tree returns to an
      already visited node.
      Unification performs a circularity check. If a circular type is found,
      exception [Cyclic_type] is raised and the type will be left cyclic, e.g.
      for error reporting. 
  *)
  val dfs_cycles: t -> t list
                         
  (** Checks if type is a syntax tree. *)
  val is_acyclic : t -> bool
end

(** Make a union-find type repesentation for the given signature. *)
module Make(Sgn : Typesgn) :
  S with type 'a Sgn.t = 'a Sgn.t
