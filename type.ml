open Core.Std
type t =
   { mutable desc : desc;
     mutable mark : int;
     id : int
   }
and desc =
  | Link of t
  | Var
  | Base of Basetype.t
  | FunW of Basetype.t * t
  | FunU of Basetype.t * t * t
with sexp

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

type type_t = t with sexp

let children a =
  match finddesc a with
  | Var | Base _ -> []
  | FunW(_, b) -> [b]
  | FunU(_, b1, b2) -> [b1; b2]
  | Link _ -> assert false

let rec subst (f: t -> t) (fbase: Basetype.t -> Basetype.t) (b: t) : t =
  match (find b).desc with
    | Var -> f (find b)
    | Base(a) -> newty (Base(Basetype.subst fbase a))
    | FunW(b1, b2) -> newty (FunW(Basetype.subst fbase b1, subst f fbase b2))
    | FunU(a1, b1, b2) -> newty(FunU(Basetype.subst fbase a1, subst f fbase b1, subst f fbase b2))
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
        | FunW(u1, u2), FunW(v1, v2) ->
          (Basetype.equals u1 v1) && (equals u2 v2)
        | FunU(u1, u2, u3), FunU(v1, v2, v3) ->
          (Basetype.equals u1 v1) && (equals u2 v2) && (equals u3 v3)
        | Link _, _ | _, Link _ -> assert false
        | Var, _ | Base _, _ | FunW _, _ | FunU _, _ ->
          false

module Typetbl = Hashtbl.Make(
struct
  type t = type_t with sexp
  let compare s t = Int.compare s.id t.id
  let hash s = s.id
end)

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

let rec freshen_index_types (a: t) : t =
    match (find a).desc with
      | Var | Base _ -> a
      | FunW(a, b1) ->
        newty(FunW(a, freshen_index_types b1))
      | FunU(_, b1, b2) ->
        newty(FunU(Basetype.newty Basetype.Var,
                   freshen_index_types b1,
                   freshen_index_types b2))
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
        Basetype.newty Basetype.OneW,
        a
      | FunW(a, b2) -> 
        let bm2, bp2 = qap b2 in
        let open Basetype in
        newty (TensorW(a, bm2)),
        bp2
      | FunU(a, b1, b2) ->
          let bm1, bp1 = qap b1 in
          let bm2, bp2 = qap b2 in
          let open Basetype in
            newty (DataW(Data.sumid 2, [newty (TensorW(a, bp1)); bm2])),
            newty (DataW(Data.sumid 2, [newty (TensorW(a, bm1)); bp2]))
      | Link _ -> assert false
  in qap s
