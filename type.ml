open Core.Std

type 'a sgn =
  | Base of Basetype.t
  | Tensor of 'a * 'a
  | FunV of Basetype.t * 'a
  | FunI of Basetype.t * 'a * 'a
with sexp
  
module Sig = struct

  type 'a t = 'a sgn with sexp                  

  let map (f : 'a -> 'b) (t : 'a t) : 'b t =
    match t with
    | Base(a) -> Base(a)
    | Tensor(x, y) -> Tensor(f x, f y)
    | FunV(a, x) -> FunV(a, f x)
    | FunI(a, x, y) -> FunI(a, f x, f y)

  let children (t: 'a t) : 'a list =
    match t with
    | Base(_) -> []
    | Tensor(x, y) -> [x; y]
    | FunV(_, x) -> [x]
    | FunI(_, x, y) -> [x; y]

  let equals (s: 'a t) (t: 'a t) ~equals:(equals: 'a -> 'a -> bool) : bool =
    match s, t with
    | Base(a1), Base(b1) ->
      Basetype.equals a1 b1
    | Tensor(t1, t2), Tensor(s1, s2) ->
      equals t1 s1 && equals t2 s2
    | FunV(a1, t2), FunV(b1, s2) ->
      Basetype.equals a1 b1 && equals t2 s2
    | FunI(a1, t1, t2), FunI(b1, s1, s2) ->
      Basetype.equals a1 b1 && equals t1 s1 && equals t2 s2;
    | Base _, _ | Tensor _ , _ | FunV _, _ | FunI _, _ ->
      false

  let unify_exn (s: 'a t) (t: 'a t) ~unify:(unify: 'a -> 'a -> unit) : unit =
    match s, t with
    | Base(a1), Base(b1) ->
      Basetype.unify_exn a1 b1
    | Tensor(t1, t2), Tensor(s1, s2) ->
      unify t1 s1;
      unify t2 s2;
    | FunV(a1, t2), FunV(b1, s2) ->
      Basetype.unify_exn a1 b1;
      unify t2 s2
    | FunI(a1, t1, t2), FunI(b1, s1, s2) ->
      Basetype.unify_exn a1 b1;
      unify t1 s1;
      unify t2 s2;
    | Base _, _ | Tensor _ , _ | FunV _, _ | FunI _, _ ->
      raise Uftype.Constructor_mismatch
end

module Type = Uftype.Make(Sig)
include Type

let rec full_subst (b: t) (f: t -> t) (fbase: Basetype.t -> Basetype.t) : t =
  match case b with
  | Var -> subst b f
  | Sgn bs ->
    match bs with
    | Base(a) -> newty (Base(Basetype.subst a fbase))
    | Tensor(b1, b2) ->
      newty(Tensor(full_subst b1 f fbase, full_subst b2 f fbase))
    | FunV(b1, b2) ->
      newty (FunV(Basetype.subst b1 fbase, full_subst b2 f fbase))
    | FunI(a1, b1, b2) ->
      newty(FunI(Basetype.subst a1 fbase,
                 full_subst b1 f fbase,
                 full_subst b2 f fbase))

let rec map_index_types (a: t) (f: Basetype.t -> Basetype.t) : t =
  match case a  with
  | Var -> a
  | Sgn sa ->
    match sa with
    | Base _ -> a
    | Tensor(b1, b2) ->
      newty(Tensor(map_index_types b1 f,
                   map_index_types b2 f))
    | FunV(a, b1) ->
      newty(FunV(a, map_index_types b1 f))
    | FunI(a, b1, b2) ->
      newty(FunI(f a,
                 map_index_types b1 f,
                 map_index_types b2 f))

let question_answer_pair (s: t) : Basetype.t * Basetype.t =
  let vm = Int.Table.create () in
  let rec qap t =
    match case t with
    | Var ->
        begin
          match Int.Table.find vm (repr_id t) with
          | Some mp -> mp
          | None ->
            let betam = Basetype.newvar() in
            let betap = Basetype.newvar() in
            Int.Table.replace vm ~key:(repr_id t) ~data:(betam, betap);
            betam, betap
        end
    | Sgn st ->
      match st with
      | Base(a) ->
        Basetype.newty Basetype.UnitB,
        a
      | Tensor(b1, b2) ->
        let bm1, bp1 = qap b1 in
        let bm2, bp2 = qap b2 in
        let open Basetype in
        newty (DataB(Data.sumid 2, [bm1; bm2])),
        newty (DataB(Data.sumid 2, [bp1; bp2]))
      | FunV(a, b2) ->
        let bm2, bp2 = qap b2 in
        let open Basetype in
        newty (PairB(a, bm2)),
        bp2
      | FunI(a, b1, b2) ->
        let bm1, bp1 = qap b1 in
        let bm2, bp2 = qap b2 in
        let open Basetype in
        newty (DataB(Data.sumid 2, [newty (PairB(a, bp1)); bm2])),
        newty (DataB(Data.sumid 2, [newty (PairB(a, bm1)); bp2]))
  in qap s


TEST_MODULE = struct

  TEST "cyclic sub-basetypes" =
    let open Basetype in
    let a = newvar () in
    let aa = newty (PairB(a, a)) in
    let b = Type.newvar() in
    let abb = Type.newty (FunI(a, b, b)) in
    let aabb = Type.newty (FunI(aa, b, b)) in
    try
      Type.unify_exn abb aabb;
      false
    with
    | Uftype.Cyclic_type -> true

end
