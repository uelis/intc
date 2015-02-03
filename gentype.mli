open Core.Std

module type Typesgn = sig
  type 'a t with sexp

  val map: ('a -> 'b) -> 'a t -> 'b t
  val children: 'a t -> 'a list

  val eq_exn: 'a t -> 'a t -> eq:('a -> 'a -> unit) -> unit
    
  val unify_exn: 'a t -> 'a t -> unify:('a -> 'a -> unit) -> unit
end

exception Not_equal
exception Not_unifiable

module type S = sig
  type t with sexp

  module Sgn : Typesgn
  type 'a var_or_sgn =
    | Var
    | Sgn of 'a Sgn.t

  val repr_id : t -> int
  
  val newvar : unit -> t

  (** Construct a fresh syntax tree node with the given description.
      The description may contain references to the children. *)
  val newty : t Sgn.t -> t
    
  val free_vars: t -> t list

  val freshen: t -> t
    
  val freshen_list: t list -> t list

  val replace_by_fresh_var: t -> unit
    
  val subst: t -> (t -> t) -> t

  (** [case x] return the description of the node [find x]. *)
  val case : t -> t var_or_sgn

  val identical : t -> t -> bool

  (** Equality of types. *)
  val equals : t -> t -> bool

  val unify_exn : t -> t -> unit
    
  val dfs_cycles: t -> t list
                         
  val is_acyclic : t -> bool
end

module Make(Sgn : Typesgn) :
  S with type 'a Sgn.t = 'a Sgn.t
