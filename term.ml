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
  | Cintslt
  | Cintprint
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
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
  | PairV of (t * Basetype.t) * (t * Basetype.t)
  | FstV of t * Basetype.t * Basetype.t
  | SndV of t * Basetype.t * Basetype.t
  | InV of (Basetype.Data.id * int * t) * Basetype.t
  | Select of Basetype.Data.id * (Basetype.t list) * t * int
  (* interaction terms *)
  | Const of op_const
  | Return of t * Basetype.t
  | Bind of (t * Basetype.t) * (var * t)
  | Fn of (var * Basetype.t) * t
  | Fun of (var * Basetype.t * Type.t) * t
  | App of t * Type.t * t
  | Case of Basetype.Data.id * (Basetype.t list) * t * ((var * t) list)
  | CopyU of t * (var * var * t)
  | Pair of t * t
  | LetPair of t* ((var * Type.t) * (var * Type.t) * t)
  | HackU of Type.t * t
  | ExternalU of (string * Type.t (* type schema *)) * Type.t
  | TypeAnnot of t * Type.t

let mkTerm d = { desc = d; loc = None }
let mkVar x = { desc = Var(x); loc = None }
let mkConstV n = { desc = ConstV(n); loc = None }
let mkConst n = { desc = Const(n); loc = None }
let mkUnitV = { desc = UnitV; loc = None}
let mkPairV s t =
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = PairV((s, alpha), (t, beta)); loc = None }
let mkFstV s =
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = FstV(s, alpha, beta); loc = None }
let mkSndV s =
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = SndV(s, alpha, beta); loc = None }
let mkInV n k t = { desc = InV((n, k, t), Basetype.newtyvar()); loc = None }
let mkInlV t =
  { desc = InV((Basetype.Data.sumid 2, 0, t), Basetype.newtyvar());
    loc = None }
let mkInrV t =
  { desc = InV((Basetype.Data.sumid 2, 1, t), Basetype.newtyvar());
    loc = None }
let mkCase id s l =
  let n = Basetype.Data.params id in
  let params = List.init n ~f:(fun _ -> Basetype.newtyvar ()) in
  { desc = Case(id, params, s, l); loc = None }
let mkApp s t = { desc = App(s, Type.newty Type.Var, t); loc = None }
let mkFn ((x, ty), t) = { desc = Fn((x, ty), t); loc = None }
let mkReturn v =
  let alpha = Basetype.newtyvar() in
  { desc = Return(v, alpha); loc = None }
let mkBind s (x ,t) =
  let alpha = Basetype.newtyvar() in
  { desc = Bind((s, alpha), (x, t)); loc = None }
let mkFun ((x, a, ty), t) = { desc = Fun((x, a, ty), t); loc = None }
let mkCopyU s ((x, y), t) = { desc = CopyU(s, (x, y, t)); loc = None }
let mkHackU ty t = { desc = HackU(ty, t); loc = None }
let mkTypeAnnot t a = { desc = TypeAnnot(t, a); loc = None }
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
  | InV((_,_,s), _) | FstV(s, _, _) | SndV(s, _, _)
  | Select(_, _, s, _) -> is_value s
  | PairV((s, _), (t, _)) -> is_value s && is_value t
  | Case _ | Const _ | App _
  | Return _ | Bind _
  | Pair _ | LetPair _
  | HackU _ | ExternalU _ | CopyU _ | Fn _ | Fun _
  | TypeAnnot _ ->
    false

let rec free_vars (term: t) : var list =
  let abs x l = List.filter l ~f:(fun z -> not (String.equal z x)) in
  match term.desc with
  | Var(v) -> [v]
  | ConstV _ | Const(_) | UnitV | ExternalU _ -> []
  | InV((_,_,s), _) | FstV(s, _, _) | SndV(s, _, _)
  | Select(_, _, s, _)  | Return(s, _)
  | HackU(_, s) -> free_vars s
  | PairV((s, _), (t, _)) | App(s, _, t) ->
    (free_vars s) @ (free_vars t)
  | CopyU(s, (x, y, t)) ->
    (free_vars s) @ (abs x (abs y (free_vars t)))
  | Fn((x, _), t) | Fun((x, _, _), t) ->
    abs x (free_vars t)
  | Bind((s, _), (x, t)) ->
    (free_vars s) @ (abs x (free_vars t))
  | Pair(s, t) ->
    (free_vars s) @ (free_vars t)
  | LetPair(s, ((x, _), (y, _), t)) ->
    (free_vars s) @ (abs x (abs y (free_vars t)))
  | Case(_, _, s, l) ->
    free_vars s @
    List.fold_right l ~f:(fun (x, t) fv -> (abs x (free_vars t)) @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    free_vars t

let rec all_vars (term: t) : var list =
  match term.desc with
  | Var(v) -> [v]
  | ConstV _ | Const(_) | UnitV | ExternalU _ -> []
  | InV((_,_,s), _) | FstV(s, _, _) | SndV(s, _, _)
  | Return(s, _) | Select(_, _, s, _)
  | HackU(_, s) -> all_vars s
  | PairV((s, _), (t, _)) | App(s, _, t)
  | CopyU(s, (_, _, t)) ->
    all_vars s @ all_vars t
  | Fn((x, _), t) | Fun((x, _, _), t) ->
    x :: all_vars t
  | Bind((s, _), (x, t)) ->
    x :: all_vars s @ all_vars t
  | Pair(s, t) ->
    (all_vars s) @ (all_vars t)
  | LetPair(s, (_, _, t)) ->
    (all_vars s) @ (all_vars t)
  | Case(_, _, s, l) ->
    all_vars s @
    List.fold_right l ~f:(fun (x, t) fv -> x :: all_vars t @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    all_vars t

let rename_vars (f: var -> var) (term: t) : t =
  let rec rn term =
    match term.desc with
    | Var(x) -> { term with desc = Var(f x) }
    | ConstV _ | Const _  | UnitV | ExternalU _ ->
      term
    | InV((n, k, s), a) ->
      { term with desc = InV((n, k, rn s), a) }
    | FstV(s, a, b) ->
      { term with desc = FstV(rn s, a, b) }
    | SndV(s, a, b) ->
      { term with desc = SndV(rn s, a, b) }
    | HackU(ty, s) ->
      { term with desc = HackU(ty, rn s) }
    | Return(s, a) ->
      { term with desc = Return(rn s, a) }
    | PairV((s, a), (t, b)) ->
      { term with desc = PairV((rn s, a), (rn t, b)) }
    | App(s, a, t) ->
      { term with desc = App(rn s, a, rn t) }
    | CopyU(s, (x, y, t)) ->
      { term with desc = CopyU(rn s, (f x, f y, rn t)) }
    | Fn((x, ty), t) ->
      { term with desc = Fn((f x, ty), rn t) }
    | Fun((x, a, ty), t) ->
      { term with desc = Fun((f x, a, ty), rn t) }
    | Bind((s, a), (x, t)) ->
      { term with desc = Bind((rn s, a), (f x, rn t)) }
    | Pair(s, t) ->
      { term with desc = Pair(rn s, rn t) }
    | LetPair(s, ((x, a), (y, b), t)) ->
      { term with desc = LetPair(rn s, ((f x, a), (f y, b), rn t)) }
    | Select(id, params, s, i) ->
      { term with desc = Select(id, params, rn s, i) }
    | Case(id, params, s, l) ->
      { term with desc = Case(id, params, rn s,
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
    | UnitV | ConstV _ | Const _ | ExternalU _ ->
      term
    | InV((n, k, s), a) ->
      {term with desc = InV((n, k, sub sigma s), a)}
    | FstV(s, a, b) ->
      { term with desc = FstV(sub sigma s, a, b) }
    | SndV(s, a, b) ->
      { term with desc = SndV(sub sigma s, a, b) }
    | HackU(ty, s) ->
      {term with desc = HackU(ty, sub sigma s)}
    | Return(s, a) ->
      { term with desc = Return(sub sigma s, a) }
    | PairV((s, a), (t, b)) ->
      { term with desc = PairV((sub sigma s, a), (sub sigma t, b)) }
    | App (s, a, t) ->
      { term with desc = App(sub sigma s, a, sub sigma t) }
    | CopyU(s, (x, y, t)) ->
      { term with desc = CopyU(sub sigma s, abs2 sigma (x, y, t)) }
    | Fn((x, ty), t) ->
      let (x', t') = abs sigma (x, t) in
      { term with desc = Fn((x', ty), t') }
    | Fun((x, a, ty), t) ->
      let (x', t') = abs sigma (x, t) in
      { term with desc = Fun((x', a, ty), t') }
    | Bind((s, a), (x, t)) ->
      { term with desc = Bind((sub sigma s, a), abs sigma (x, t)) }
    | Pair(s, t) ->
      { term with desc = Pair(sub sigma s, sub sigma t) }
    | LetPair(s, ((x, a), (y, b), t)) ->
      let x', y', t' = abs2 sigma (x, y, t) in
      { term with desc = LetPair(sub sigma s, ((x', a), (y', b), t')) }
    | Select(id, params, s, i) ->
      { term with desc = Select(id, params, sub sigma s, i) }
    | Case(id, params, s, l) ->
      { term with desc = Case(id, params, sub sigma s,
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

(* Conveniencene function for n-ary Bind  *)
let mkBindList (x: var) ((sigma: var list), (f: t)) : t =
  let rec remove_shadow sigma =
    match sigma with
    | [] -> []
    | x :: rest ->
      x :: remove_shadow
            (List.map rest
                ~f:(fun y -> if x = y then unusable_var else y))
  in
  let xs = all_vars f in
  let fresh_var = Vargen.mkVarGenerator "z" ~avoid:(x :: xs @ sigma) in
  let rec let_tuple z (sigma, f) =
    match sigma with
    | [] -> f
    | y :: rest ->
      let z1 = fresh_var () in
       subst (mkSndV (mkVar z)) y
         (subst (mkFstV (mkVar z)) z1
            (let_tuple z1 (rest, f))) in
  let_tuple x (remove_shadow sigma, f)

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
    | Const(Cintslt)
    | Const(Cintprint)
    | Const(Cprint _) ->
      term
    | InV((n, k, s), a) ->
      { term with desc = InV((n, k, mta s), fbase a) }
    | FstV(s, a, b) ->
      { term with desc = FstV(mta s, fbase a, fbase b) }
    | SndV(s, a, b) ->
      { term with desc = SndV(mta s, fbase a, fbase b) }
    | Return(s, a) ->
      { term with desc = Return(mta s, fbase a) }
    | PairV((s, a), (t, b)) ->
      { term with desc = PairV((mta s, fbase a), (mta t, fbase b)) }
    | App(s, a, t) ->
      { term with desc = App(mta s, f a, mta t) }
    | CopyU(s, (x, y, t)) ->
      { term with desc = CopyU(mta s, (x, y, mta t)) }
    | Fn((x, a), t) ->
      { term with desc = Fn((x, fbase a), mta t) }
    | Fun((x, a, ty), t) ->
      { term with desc = Fun((x, fbase a, f ty), mta t) }
    | Bind((s, a), (x, t)) ->
      { term with desc = Bind((mta s, fbase a), (x, mta t)) }
    | Pair(s, t) ->
      { term with desc = Pair(mta s, mta t) }
    | LetPair(s, ((x, a), (y, b), t)) ->
      { term with desc = LetPair(mta s, ((x, f a), (y, f b), mta t)) }
    | Select(id, params, s, i) ->
      { term with desc = Select(id, List.map params ~f:fbase, mta s, i) }
    | Case(id, params, s, l) ->
      { term with desc = Case(id, List.map params ~f:fbase, mta s,
                              List.map l ~f:(fun (x, t) -> (x, mta t))) }
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(mta t, f ty) }
    | HackU(ty, s) -> { term with desc = HackU(f ty, mta s) }
    | ExternalU(e, ty) -> { term with desc = ExternalU(e, f ty) }
  in mta t
