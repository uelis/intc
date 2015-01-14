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

  let rec unify_raw (c : type_eq) : unit =
    match c with
    | Basetype_eq(b1, b2, tag) ->
      begin
        let open Basetype in
        let c1, c2 = find b1, find b2 in
        if not (phys_equal c1 c2) then
          match finddesc c1, finddesc c2 with
          | Var, _ ->
            union c1 c2
          | _, Var ->
            union c2 c1
          | IntB, IntB
          | ZeroB, ZeroB
          | UnitB, UnitB ->
            ()
          | BoxB(t1), BoxB(s1) ->
            unify_raw (Basetype_eq(t1, s1, tag))
          | ArrayB(t1), ArrayB(s1) ->
            unify_raw (Basetype_eq(t1, s1, tag))
          | PairB(t1, t2), PairB(s1, s2) ->
            unify_raw (Basetype_eq(t1, s1, tag));
            unify_raw (Basetype_eq(t2, s2, tag))
          | DataB(i, ts), DataB(j, ss) when i = j ->
            List.iter
              ~f:(fun (t, s) -> unify_raw (Basetype_eq (t, s, tag)))
              (List.zip_exn ts ss)
          | IntB, _ | ZeroB, _ | UnitB, _
          | BoxB _, _ | ArrayB _, _ | PairB _, _ | DataB _, _ ->
            raise (Not_Unifiable (Equation_failed c))
          | Link _, _ -> assert false
      end
    | Type_eq(t1, t2, tag) ->
      begin
        let open Type in
        let c1, c2 = find t1, find t2 in
        if not (phys_equal c1 c2) then
          match finddesc c1, finddesc c2 with
          | Var, _ ->
            union c1 c2
          | _, Var ->
            union c2 c1
          | Base(t1), Base(s1) ->
            unify_raw (Basetype_eq (t1, s1, tag))
          | Tensor(t1, t2), Tensor(s1, s2) ->
            unify_raw (Type_eq (t1, s1, tag));
            unify_raw (Type_eq (t2, s2, tag))
          | FunV(a1, t2), FunV(b1, s2) ->
            unify_raw (Basetype_eq (a1, b1, tag));
            unify_raw (Type_eq (t2, s2, tag))
          | FunI(a1, t1, t2), FunI(b1, s1, s2) ->
            unify_raw (Basetype_eq (a1, b1, tag));
            unify_raw (Type_eq (t1, s1, tag));
            unify_raw (Type_eq (t2, s2, tag))
          | Base _, _ | Tensor _ , _ | FunV _, _ | FunI _, _ ->
            raise (Not_Unifiable (Equation_failed c))
          | Link _, _ -> assert false
      end

  module TypeAlgs = Types.Algs(Type)
  module BasetypeAlgs = Types.Algs(Basetype)

  let check_cycle (c: type_eq) : unit =
    let check_basetype b = 
      if not (BasetypeAlgs.is_acyclic b) then
        raise (Not_Unifiable(Cyclic_type(c))) in
    let rec check_sub_basetypes t =
      match Type.finddesc t with
      | Type.Var -> ()
      | Type.Base(b) ->
        check_basetype b
      | Type.Tensor(t1, t2) ->
        check_sub_basetypes t1;
        check_sub_basetypes t2
      | Type.FunV(a, t1) ->
        check_basetype a;
        check_sub_basetypes t1
      | Type.FunI(a, t1, t2) ->
        check_basetype a;
        check_sub_basetypes t1;
        check_sub_basetypes t2
      | Type.Link _ -> assert false in
    let check_type t = 
      if not (TypeAlgs.is_acyclic t) then
        raise (Not_Unifiable(Cyclic_type(c)));
      check_sub_basetypes t in
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
    let a = newtyvar () in
    let aa = newty (PairB(a, a)) in
    let b = Type.newty Type.Var in
    let abb = Type.newty (Type.FunI(a, b, b)) in
    let aabb = Type.newty (Type.FunI(aa, b, b)) in
    try
      U.unify_eqs [U.Type_eq(abb, aabb, None)];
      false
    with
    | U.Not_Unifiable(U.Cyclic_type(_)) -> true

end
