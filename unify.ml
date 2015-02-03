(** Unification
 *
 * The unification algorithm loosely follows the
 * description in Section 1.4 of the following article:
 *   Didier Rémy. Using, Understanding, and Unraveling
 *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
 *   http://pauillac.inria.fr/~remy/cours/appsem/
*)
open Core.Std

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

module Make(Tag : T) = struct

  type tag = Tag.t

  type type_eq =
    | Type_eq of Type.t * Type.t * (tag option)
    | Basetype_eq of Basetype.t * Basetype.t * (tag option)

  type failure_reason =
    | Equation_failed of type_eq
    | Cyclic_type of type_eq

  exception Not_Unifiable of failure_reason

  let unify_raw (c : type_eq) : unit =
    match c with
    | Basetype_eq(b1, b2, _) ->
      begin
        try
          Basetype.unify_exn b1 b2
        with
        | Gentype.Cyclic_type -> raise (Not_Unifiable (Cyclic_type c))
        | Gentype.Not_unifiable -> raise (Not_Unifiable (Equation_failed c))
      end
    | Type_eq(t1, t2, tag) ->
      begin
        try
          Type.unify_exn t1 t2
        with
        | Gentype.Cyclic_type -> raise (Not_Unifiable (Cyclic_type c))
        | Gentype.Not_unifiable -> raise (Not_Unifiable (Equation_failed c))
      end


  let check_cycle (c: type_eq) : unit =
    let check_basetype b =
      if not (Basetype.is_acyclic b) then
        raise (Not_Unifiable(Cyclic_type(c))) in
    let check_type t =
      if not (Type.is_acyclic t) then
        raise (Not_Unifiable(Cyclic_type(c))) in
    match c with
    | Basetype_eq(b, _, _) -> check_basetype b
    | Type_eq(t, _, _) -> check_type t

  let unify_with_cycle_check (e : type_eq) : unit =
    unify_raw e;
    check_cycle e

  let unify_eqs (eqs: type_eq list): unit =
    List.iter ~f:unify_with_cycle_check eqs

  let unify (t1 : Basetype.t) (t2 : Basetype.t) : unit =
    unify_with_cycle_check (Basetype_eq (t1, t2, None))

end


TEST_MODULE = struct

  module U = Make(Unit)

  TEST "cyclic sub-basetypes" =
    let open Basetype in
    let a = newvar () in
    let aa = newty (PairB(a, a)) in
    let b = Type.newvar() in
    let abb = Type.newty (Type.FunI(a, b, b)) in
    let aabb = Type.newty (Type.FunI(aa, b, b)) in
    try
      U.unify_eqs [U.Type_eq(abb, aabb, None)];
      false
    with
    | U.Not_Unifiable(U.Cyclic_type(_)) -> true

end
