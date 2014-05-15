
module type S = sig

  type tag

  type type_eq = 
    | Type_eq of Type.t * Type.t * (tag option)
    | Basetype_eq of Basetype.t * Basetype.t * (tag option)

  type failure_reason =
    | Equation_failed of type_eq
    | Cyclic_type of type_eq 

  exception Not_Unifiable of failure_reason

  val unify_eqs: type_eq list -> unit

  val unify: Basetype.t -> Basetype.t -> unit

end

module Unify(Tag : sig type t end) : S 
               with type tag = Tag.t                                     
