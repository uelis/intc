(** Unification
 *
 * The unification algorithm loosely follows the
 * description in Section 1.4 of the following article:
 *   Didier Rémy. Using, Understanding, and Unraveling
 *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
 *   http://pauillac.inria.fr/~remy/cours/appsem/
*)

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

module Unify(T : sig type t end) = struct

  type tag = T.t

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
        if c1 != c2 then
          match finddesc c1, finddesc c2 with
          | Var, _ ->
            union c1 c2
          | _, Var ->
            union c2 c1
          | NatW, NatW 
          | ZeroW, ZeroW 
          | OneW, OneW -> 
            ()
          | BoxW(t1), BoxW(s1) ->
            unify_raw (Basetype_eq(t1, s1, tag))
          | TensorW(t1, t2), TensorW(s1, s2) ->
            unify_raw (Basetype_eq(t1, s1, tag));
            unify_raw (Basetype_eq(t2, s2, tag))
          | DataW(i, ts), DataW(j, ss) when i = j -> 
            List.iter 
              (fun (t, s) -> unify_raw (Basetype_eq (t, s, tag)))
              (List.combine ts ss)
          | NatW, _ | ZeroW, _ | OneW, _ 
          | BoxW _, _ | TensorW _, _ | DataW _, _ ->
            raise (Not_Unifiable (Equation_failed c))
          | Link _, _ -> assert false
      end
    | Type_eq(t1, t2, tag) -> 
      begin
        let open Type in
        let c1, c2 = find t1, find t2 in
        if c1 != c2 then
          match finddesc c1, finddesc c2 with
          | Var, _ ->
            union c1 c2
          | _, Var ->
            union c2 c1
          | FunW(t1, t2), FunW(s1, s2) ->
            unify_raw (Basetype_eq (t1, s1, tag));
            unify_raw (Basetype_eq (t2, s2, tag))
          | FunU(a1, t1, t2), FunU(b1, s1, s2) -> 
            unify_raw (Basetype_eq (a1, b1, tag));
            unify_raw (Type_eq (t1, s1, tag));
            unify_raw (Type_eq (t2, s2, tag))
          | FunW _, _ | FunU _, _ ->
            raise (Not_Unifiable (Equation_failed c))
          | Link _, _ -> assert false
      end

  module TypeAlgs = Types.Algs(Type)
  module BasetypeAlgs = Types.Algs(Basetype)

  let check_cycle (c: type_eq) : unit =
    match c with 
    | Basetype_eq(t, _, _) ->
      if not (BasetypeAlgs.is_acyclic t) then 
        raise (Not_Unifiable(Cyclic_type(c)))
    | Type_eq(t, _, _) -> 
      if not (TypeAlgs.is_acyclic t) then 
        raise (Not_Unifiable(Cyclic_type(c)))

  let unify_with_cycle_check (e : type_eq) : unit =
    unify_raw e;
    check_cycle e

  let unify_eqs (eqs: type_eq list): unit =
    List.iter unify_with_cycle_check eqs

  let unify (t1 : Basetype.t) (t2 : Basetype.t) : unit =
    unify_with_cycle_check (Basetype_eq (t1, t2, None))

end      
