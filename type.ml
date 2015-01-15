open Core.Std

module T = struct

  type t =
    { mutable desc : desc;
      mutable mark : int;
      id : int
    }
  and desc =
    | Link of t
    | Var
    | Base of Basetype.t
    | Tensor of t * t
    | FunV of Basetype.t * t
    | FunI of Basetype.t * t * t
  with sexp

  let compare s t = Int.compare s.id t.id
  let hash s = s.id
end

include T

let next_id = ref 0
let newty d =
  incr next_id; { desc = d; mark = 0; id = !next_id }

let phys_id t = t.id

let current_mark : int ref = ref 0
let next_mark () : int = incr current_mark; !current_mark

let set_mark t i =
  t.mark <- i

let get_mark t =
  t.mark

let rec find (t : t) : t =
    match t.desc with
    | Link l ->
        let r = find l
        in t.desc <- Link r;
           r
    | _ -> t

let finddesc (t : t) = (find t).desc

let union (t1 : t) (t2 : t) : unit =
  (find t1).desc <- Link (find t2)

let children a =
  match finddesc a with
  | Var | Base _ -> []
  | Tensor(b1, b2) -> [b1; b2]
  | FunV(_, b) -> [b]
  | FunI(_, b1, b2) -> [b1; b2]
  | Link _ -> assert false

let rec subst (f: t -> t) (fbase: Basetype.t -> Basetype.t) (b: t) : t =
  match (find b).desc with
    | Var -> f (find b)
    | Base(a) -> newty (Base(Basetype.subst fbase a))
    | Tensor(b1, b2) -> newty(Tensor(subst f fbase b1, subst f fbase b2))
    | FunV(b1, b2) -> newty (FunV(Basetype.subst fbase b1, subst f fbase b2))
    | FunI(a1, b1, b2) -> newty(FunI(Basetype.subst fbase a1, subst f fbase b1, subst f fbase b2))
    | Link _ -> assert false

let rec equals (u: t) (v: t) : bool =
  let ur = find u in
  let vr = find v in
    if ur.id = vr.id then true
    else
      match ur.desc, vr.desc with
        | Var, Var ->
          false
        | Base(a1), Base(a2) ->
          Basetype.equals a1 a2
        | Tensor(u1, u2), Tensor(v1, v2) ->
          (equals u1 v1) && (equals u2 v2)
        | FunV(u1, u2), FunV(v1, v2) ->
          (Basetype.equals u1 v1) && (equals u2 v2)
        | FunI(u1, u2, u3), FunI(v1, v2, v3) ->
          (Basetype.equals u1 v1) && (equals u2 v2) && (equals u3 v3)
        | Link _, _ | _, Link _ -> assert false
        | Var, _ | Base _, _ | Tensor _, _ | FunV _, _ | FunI _, _ ->
          false

module Typetbl = Hashtbl.Make(T)

let freshen t =
  let vm = Typetbl.create () in
  let vbasem = Int.Table.create () in
  let f x =
    match Typetbl.find vm (find x) with
    | Some y -> y
    | None ->
      let y = newty Var in
      Typetbl.replace vm ~key:(find x) ~data:y;
      y in
  let fbase x =
    match Int.Table.find vbasem (Basetype.find x).Basetype.id with
    | Some y -> y
    | None ->
      let y = Basetype.newty Basetype.Var in
      Int.Table.replace vbasem ~key:(Basetype.find x).Basetype.id ~data:y;
      y in
  subst f fbase t

let rec map_index_types (a: t) (f: Basetype.t -> Basetype.t) : t =
    match (find a).desc with
      | Var | Base _ -> a
      | Tensor(b1, b2) ->
        newty(Tensor(map_index_types b1 f,
                     map_index_types b2 f))
      | FunV(a, b1) ->
        newty(FunV(a, map_index_types b1 f))
      | FunI(a, b1, b2) ->
        newty(FunI(f a,
                   map_index_types b1 f,
                   map_index_types b2 f))
      | Link _ -> assert false

let question_answer_pair (s: t) : Basetype.t * Basetype.t =
  let vm = Typetbl.create () in
  let rec qap t =
    match (find t).desc with
      | Var ->
        begin
          match Typetbl.find vm (find t) with
          | Some mp -> mp
          | None ->
            let betam = Basetype.newty Basetype.Var in
            let betap = Basetype.newty Basetype.Var in
            Typetbl.replace vm ~key:(find t) ~data:(betam, betap);
            betam, betap
          end
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
      | Link _ -> assert false
  in qap s
