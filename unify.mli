(** Unification of types *)
open Core.Std

module type S = sig

  (** Equations can be tagged with type [tag] for error reporting.
      Should unification of an equation fail, the tag will be
      returned to identify that equation. *)
  type tag

  (** Type equations *)
  type type_eq =
    | Type_eq of Type.t * Type.t * (tag option)
    | Basetype_eq of Basetype.t * Basetype.t * (tag option)

  type failure_reason =
    | Equation_failed of type_eq
    | Cyclic_type of type_eq

  exception Not_Unifiable of failure_reason

  (** Unify a list of equations *)
  val unify_eqs: type_eq list -> unit

  (** Unify two base types without tags. This is a
      convenient special case of [unify_eqs]. *)
  val unify: Basetype.t -> Basetype.t -> unit

end

module Make(EqTag : T) :
  S with type tag = EqTag.t
