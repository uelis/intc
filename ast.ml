(** Term representation *)

(*  I've read the implementation of John Harrion's HOL light
    and the sources of the OCaml compiler when writing this file. *)

open Core.Std

type var = string

let unusable_var = "_unusable"

module Location = struct
  type pos = { column: int; line: int}
  type loc = {start_pos: pos; end_pos: pos}
  type t = loc option
  let none = None
end

type value_const =
  | Cundef of Basetype.t
  | Cintconst of int

type op_const =
  | Cprint of string
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintlt
  | Cintslt
  | Cintshl
  | Cintshr
  | Cintsar
  | Cintand
  | Cintor
  | Cintxor
  | Cintprint
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Carrayalloc of Basetype.t
  | Carrayfree of Basetype.t
  | Carrayget of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t
  | Cencode of Basetype.t * Basetype.t
  | Cdecode of Basetype.t * Basetype.t

type t = {
  desc: t_desc;
  loc: Location.t
}
and t_desc =
  | Var of var
  (* value terms *)
  | ConstV of value_const
  | UnitV
  | PairV of t * t
  | FstV of t
  | SndV of t
  | InV of (Basetype.Data.id * int * t)
  | SelectV of Basetype.Data.id * (Basetype.t list) * t * int
  (* interaction terms *)
  | Const of op_const
  | Return of t
  | Bind of t * (var * t)
  | Fn of (var * Basetype.t) * t
  | Fun of (var * Basetype.t * Type.t) * t
  | App of t * t
  | Case of Basetype.Data.id * t * ((var * t) list)
  | Copy of t * (var list * t)
  | Pair of t * t
  | LetPair of t * (var * var * t)
  | Direct of Type.t * t
  | TypeAnnot of t * Type.t

let mkTerm d = { desc = d; loc = None }

let mkVar x = mkTerm (Var(x))
let mkConstV n = mkTerm (ConstV(n))
let mkConst n = mkTerm (Const(n))
let mkUnitV = mkTerm UnitV
let mkPairV s t = mkTerm (PairV(s, t))
let mkFstV s = mkTerm (FstV(s))
let mkSndV s = mkTerm (SndV(s))
let mkInV n k t = mkTerm (InV((n, k, t)))
let mkInlV t = mkTerm (InV(Basetype.Data.sumid 2, 0, t))
let mkInrV t = mkTerm (InV(Basetype.Data.sumid 2, 1, t))
let mkCase id s l = mkTerm (Case(id, s, l))
let mkApp s t = mkTerm (App(s, t))
let mkFn ((x, ty), t) = mkTerm (Fn((x, ty), t))
let mkReturn v = mkTerm (Return(v))
let mkBind s (x ,t) = mkTerm (Bind(s, (x, t)))
let mkFun ((x, a, ty), t) = mkTerm (Fun((x, a, ty), t))
let mkCopy s (xs, t) = mkTerm (Copy(s, (xs, t)))
let mkDirect ty t = mkTerm (Direct(ty, t))
let mkTypeAnnot t a = mkTerm (TypeAnnot(t, a))
let mkBox t =
  let alpha = Basetype.newtyvar() in
  let addr = "addr" in
  mkBind (mkApp (mkConst (Calloc alpha)) mkUnitV)
    (addr, mkBind (mkApp (mkConst (Cstore alpha)) (mkPairV (mkVar addr) t))
             (unusable_var, mkReturn (mkVar addr)))
let mkUnbox t =
  let alpha = Basetype.newtyvar() in
  let v = "val" in
  mkBind (mkApp (mkConst (Cload alpha)) t)
    (v, mkBind (mkApp (mkConst (Cfree alpha)) t)
          (unusable_var, mkReturn (mkVar v)))

let rec is_value (term: t) : bool =
  match term.desc with
  | Var _ | ConstV _ | UnitV -> true
  | InV(_,_,s) | FstV(s) | SndV(s)
  | SelectV(_, _, s, _) -> is_value s
  | PairV(s, t) -> is_value s && is_value t
  | Case _ | Const _ | App _
  | Return _ | Bind _
  | Pair _ | LetPair _
  | Direct _ | Copy _ | Fn _ | Fun _
  | TypeAnnot _ ->
    false

let rec free_vars (term: t) : var list =
  let abs x l = List.filter l ~f:(fun z -> not (String.equal z x)) in
  let abs_list xs l = List.filter l ~f:(fun z -> not (List.mem xs z)) in
  match term.desc with
  | Var(v) -> [v]
  | ConstV _ | Const(_) | UnitV  -> []
  | InV(_,_,s) | FstV(s) | SndV(s)
  | SelectV(_, _, s, _)  | Return(s)
  | Direct(_, s) -> free_vars s
  | PairV(s, t) | App(s, t) ->
    (free_vars s) @ (free_vars t)
  | Copy(s, (xs, t)) ->
    (free_vars s) @ (abs_list xs (free_vars t))
  | Fn((x, _), t) | Fun((x, _, _), t) ->
    abs x (free_vars t)
  | Bind(s, (x, t)) ->
    (free_vars s) @ (abs x (free_vars t))
  | Pair(s, t) ->
    (free_vars s) @ (free_vars t)
  | LetPair(s, (x, y, t)) ->
    (free_vars s) @ (abs x (abs y (free_vars t)))
  | Case(_, s, l) ->
    free_vars s @
    List.fold_right l ~f:(fun (x, t) fv -> (abs x (free_vars t)) @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    free_vars t

let rec all_vars (term: t) : var list =
  match term.desc with
  | Var(v) -> [v]
  | ConstV _ | Const(_) | UnitV -> []
  | InV(_,_,s) | FstV(s) | SndV(s)
  | Return(s) | SelectV(_, _, s, _)
  | Direct(_, s) -> all_vars s
  | PairV(s, t) | App(s, t)
  | Copy(s, (_, t)) ->
    all_vars s @ all_vars t
  | Fn((x, _), t) | Fun((x, _, _), t) ->
    x :: all_vars t
  | Bind(s, (x, t)) ->
    x :: all_vars s @ all_vars t
  | Pair(s, t) ->
    (all_vars s) @ (all_vars t)
  | LetPair(s, (_, _, t)) ->
    (all_vars s) @ (all_vars t)
  | Case(_, s, l) ->
    all_vars s @
    List.fold_right l ~f:(fun (x, t) fv -> x :: all_vars t @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    all_vars t

let rename_vars (f: var -> var) (term: t) : t =
  let rec rn term =
    match term.desc with
    | Var(x) -> { term with desc = Var(f x) }
    | ConstV _ | Const _  | UnitV ->
      term
    | InV(n, k, s) ->
      { term with desc = InV(n, k, rn s) }
    | FstV(s) ->
      { term with desc = FstV(rn s) }
    | SndV(s) ->
      { term with desc = SndV(rn s) }
    | Direct(ty, s) ->
      { term with desc = Direct(ty, rn s) }
    | Return(s) ->
      { term with desc = Return(rn s) }
    | PairV(s, t) ->
      { term with desc = PairV(rn s, rn t) }
    | App(s, t) ->
      { term with desc = App(rn s, rn t) }
    | Copy(s, (xs, t)) ->
      { term with desc = Copy(rn s, (List.map ~f:f xs, rn t)) }
    | Fn((x, ty), t) ->
      { term with desc = Fn((f x, ty), rn t) }
    | Fun((x, a, ty), t) ->
      { term with desc = Fun((f x, a, ty), rn t) }
    | Bind(s, (x, t)) ->
      { term with desc = Bind(rn s, (f x, rn t)) }
    | Pair(s, t) ->
      { term with desc = Pair(rn s, rn t) }
    | LetPair(s, (x, y, t)) ->
      { term with desc = LetPair(rn s, (f x, f y, rn t)) }
    | SelectV(id, params, s, i) ->
      { term with desc = SelectV(id, params, rn s, i) }
    | Case(id, s, l) ->
      { term with desc = Case(id, rn s,
                              List.map l ~f:(fun (x, t) -> (f x, rn t))) }
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(rn t, ty) }
  in rn term

let variant_var x = x ^ "'"
let variant = rename_vars variant_var

let rec variant_var_avoid x avoid =
  let vx = variant_var x in
  if List.mem avoid vx then
    variant_var_avoid vx (x :: avoid)
  else
    vx

(* Renames all variables with new names drawn from
 * the given name-supply. *)
let variant_with_name_supply (fresh_var: unit -> var) (t: t) : t =
  let ren_map =
    free_vars t
    |> List.fold
         ~f:(fun m v -> String.Map.add m ~key:v ~data:(fresh_var ()))
         ~init:String.Map.empty in
  rename_vars (String.Map.find_exn ren_map) t

(* Substitues [s] for [x].
   Returns [None] if [t] does not contain [x].
   If [head] is true then only the head occurrence is subtituted.
*)
let substitute ?head:(head=false) (s: t) (x: var) (t: t) : t option =
  (* Below sigma is always a permutation that maps bound
   * variables of t to suitably fresh variables. *)
  let fvs = free_vars s in
  let apply sigma y =
    List.Assoc.find sigma y
    |> Option.value ~default:y in
  let substituted = ref false in
  let rec sub sigma term =
    match term.desc with
    | Var(y) ->
      (* substitute only once if head *)
      if x = y && ((not head) || (not !substituted)) then
        (substituted := true; s)
      else
        { term with desc = Var(apply sigma y) }
    | UnitV | ConstV _ | Const _ ->
      term
    | InV(n, k, s) ->
      {term with desc = InV(n, k, sub sigma s) }
    | FstV(s) ->
      { term with desc = FstV(sub sigma s) }
    | SndV(s) ->
      { term with desc = SndV(sub sigma s) }
    | Direct(ty, s) ->
      {term with desc = Direct(ty, sub sigma s)}
    | Return(s) ->
      { term with desc = Return(sub sigma s) }
    | PairV(s, t) ->
      { term with desc = PairV(sub sigma s, sub sigma t) }
    | App (s, t) ->
      { term with desc = App(sub sigma s, sub sigma t) }
    | Copy(s, (xs, t)) ->
      { term with desc = Copy(sub sigma s, abs_list sigma (xs, t)) }
    | Fn((x, ty), t) ->
      let (x', t') = abs sigma (x, t) in
      { term with desc = Fn((x', ty), t') }
    | Fun((x, a, ty), t) ->
      let (x', t') = abs sigma (x, t) in
      { term with desc = Fun((x', a, ty), t') }
    | Bind(s, (x, t)) ->
      { term with desc = Bind(sub sigma s, abs sigma (x, t)) }
    | Pair(s, t) ->
      { term with desc = Pair(sub sigma s, sub sigma t) }
    | LetPair(s, (x, y, t)) ->
      let x', y', t' = abs2 sigma (x, y, t) in
      { term with desc = LetPair(sub sigma s, (x', y', t')) }
    | SelectV(id, params, s, i) ->
      { term with desc = SelectV(id, params, sub sigma s, i) }
    | Case(id, s, l) ->
      { term with desc = Case(id, sub sigma s,
                              List.map l ~f:(fun (x, t) -> abs sigma (x, t))) }
    | TypeAnnot(t, ty) ->
      { term with desc = TypeAnnot(sub sigma t, ty) }
  and abs sigma (y, u) =
    match abs_list sigma ([y], u) with
    | [y'], u -> y', u
    | _ -> assert false
  and abs2 sigma (y, z, u) =
    match abs_list sigma ([y; z], u) with
    | [y'; z'], u -> y', z', u
    | _ -> assert false
  and abs_list sigma (l, t1) =
    if List.mem l x then (l, t1)
    else if List.for_all l ~f:(fun y -> not (List.mem fvs y)) then
      (* no capture *)
      (l, sub sigma t1)
    else
      (* avoid capture *)
      let avoid = fvs @ l @ (List.map ~f:(apply sigma) (free_vars t1)) in
      let l' = List.map ~f:(fun y -> variant_var_avoid y avoid) l in
      (l', sub ((List.zip_exn l l') @ sigma) t1)
  in
  let result = sub [] t in
  if (!substituted) then Some result else None

let head_subst (s: t) (x: var) (t: t) : t option =
  substitute ~head:true s x t

let subst (s: t) (x: var) (t: t) : t =
  match substitute ~head:false s x t with
  | None -> t
  | Some t' -> t'

let freshen_type_vars t =
  let new_type_vars = Int.Table.create () in
  let new_basetype_vars = Int.Table.create () in
  let fv x =
    match Int.Table.find new_type_vars (Type.find x).Type.id with
    | Some y -> y
    | None ->
      let y = Type.newty Type.Var in
      Int.Table.replace new_type_vars ~key:(Type.find x).Type.id ~data:y;
      y in
  let basefv x =
    match Int.Table.find new_basetype_vars (Basetype.find x).Basetype.id with
    | Some y -> y
    | None ->
      let y = Basetype.newty Basetype.Var in
      Int.Table.replace new_basetype_vars
        ~key:(Basetype.find x).Basetype.id ~data:y;
      y in
  let f a = Type.subst fv basefv a in
  let fbase a = Basetype.subst basefv a in
  let rec mta term =
    match term.desc with
    | Var(_) | UnitV -> term
    | ConstV(Cundef(a)) ->
      { term with desc = ConstV(Cundef(fbase a)) }
    | Const(Calloc(a)) ->
      { term with desc = Const(Calloc(fbase a)) }
    | Const(Cfree(a)) ->
      { term with desc = Const(Cfree(fbase a)) }
    | Const(Cload(a)) ->
      { term with desc = Const(Cload(fbase a)) }
    | Const(Cstore(a)) ->
      { term with desc = Const(Cstore(fbase a)) }
    | Const(Cpush(a)) ->
      { term with desc = Const(Cpush(fbase a)) }
    | Const(Cpop(a)) ->
      { term with desc = Const(Cpop(fbase a)) }
    | Const(Carrayalloc(a)) ->
      { term with desc = Const(Carrayalloc(fbase a)) }
    | Const(Carrayget(a)) ->
      { term with desc = Const(Carrayget(fbase a)) }
    | Const(Carrayfree(a)) ->
      { term with desc = Const(Carrayfree(fbase a)) }
    | Const(Ccall(s, a, b)) ->
      { term with desc = Const(Ccall(s, fbase a, fbase b)) }
    | Const(Cencode(a, b)) ->
      { term with desc = Const(Cencode(fbase a, fbase b)) }
    | Const(Cdecode(a, b)) ->
      { term with desc = Const(Cdecode(fbase a, fbase b)) }
    | ConstV(Cintconst _)
    | Const(Cintadd)
    | Const(Cintsub)
    | Const(Cintmul)
    | Const(Cintdiv)
    | Const(Cinteq)
    | Const(Cintlt)
    | Const(Cintslt)
    | Const(Cintshl)
    | Const(Cintshr)
    | Const(Cintsar)
    | Const(Cintand)
    | Const(Cintor)
    | Const(Cintxor)
    | Const(Cintprint)
    | Const(Cprint _) ->
      term
    | InV(n, k, s) ->
      { term with desc = InV(n, k, mta s) }
    | FstV(s) ->
      { term with desc = FstV(mta s) }
    | SndV(s) ->
      { term with desc = SndV(mta s) }
    | Return(s) ->
      { term with desc = Return(mta s) }
    | PairV(s, t) ->
      { term with desc = PairV(mta s, mta t) }
    | App(s, t) ->
      { term with desc = App(mta s, mta t) }
    | Copy(s, (xs, t)) ->
      { term with desc = Copy(mta s, (xs, mta t)) }
    | Fn((x, a), t) ->
      { term with desc = Fn((x, fbase a), mta t) }
    | Fun((x, a, ty), t) ->
      { term with desc = Fun((x, fbase a, f ty), mta t) }
    | Bind(s, (x, t)) ->
      { term with desc = Bind(mta s, (x, mta t)) }
    | Pair(s, t) ->
      { term with desc = Pair(mta s, mta t) }
    | LetPair(s, (x, y, t)) ->
      { term with desc = LetPair(mta s, (x, y, mta t)) }
    | SelectV(id, params, s, i) ->
      { term with desc = SelectV(id, List.map params ~f:fbase, mta s, i) }
    | Case(id, s, l) ->
      { term with desc = Case(id, mta s,
                              List.map l ~f:(fun (x, t) -> (x, mta t))) }
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(mta t, f ty) }
    | Direct(ty, s) -> { term with desc = Direct(f ty, mta s) }
  in mta t
