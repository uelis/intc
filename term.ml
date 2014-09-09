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
  | ValW of value_const 
  | ConstW of op_const 
  | UnitW 
  | PairW of (t * Basetype.t) * (t * Basetype.t)
  | FstW of t * Basetype.t * Basetype.t
  | SndW of t * Basetype.t * Basetype.t
  | InW of (Basetype.Data.id * int * t) * Basetype.t
  | BindW of (t * Basetype.t) * (var * t)
  | App of t * Type.t * t 
  | Box of t * Basetype.t
  | Unbox of t * Basetype.t
  | Case of Basetype.Data.id * (Basetype.t list) * t * ((var * t) list) 
  | Select of Basetype.Data.id * (Basetype.t list) * t * int
  | LambdaW of (var * Basetype.t) * t
  | LambdaU of (var * Basetype.t * Type.t) * t
  | CopyU of t * (var * var * t)
  | HackU of Type.t * t
  | ExternalU of (string * Type.t (* type schema *)) * Type.t
  | TypeAnnot of t * Type.t

let mkTerm d = { desc = d; loc = None }
let mkVar x = { desc = Var(x); loc = None }
let mkConstW n = { desc = ConstW(n); loc = None }
let mkUnitW = { desc = UnitW; loc = None}
let mkPairW s t = 
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = PairW((s, alpha), (t, beta)); loc = None }
let mkFstW s = 
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = FstW(s, alpha, beta); loc = None }
let mkSndW s = 
  let alpha = Basetype.newtyvar() in
  let beta = Basetype.newtyvar() in
  { desc = SndW(s, alpha, beta); loc = None }
let mkInW n k t = { desc = InW((n, k, t), Basetype.newtyvar()); loc = None }
let mkInlW t = 
  { desc = InW((Basetype.Data.sumid 2, 0, t), Basetype.newtyvar()); 
    loc = None }
let mkInrW t = 
  { desc = InW((Basetype.Data.sumid 2, 1, t), Basetype.newtyvar()); 
    loc = None }
let mkCase id s l = 
  let n = Basetype.Data.params id in
  let params = List.init n ~f:(fun _ -> Basetype.newtyvar ()) in
  { desc = Case(id, params, s, l); loc = None }
let mkApp s t = { desc = App(s, Type.newty Type.Var, t); loc = None }
let mkBox t = { desc = Box(t, Basetype.newty Basetype.Var); loc = None }
let mkUnbox t = { desc = Unbox(t, Basetype.newty Basetype.Var); loc = None }
let mkLambdaW ((x, ty), t) = { desc = LambdaW((x, ty), t); loc = None }
let mkBindW s (x ,t) = 
  let alpha = Basetype.newtyvar() in
  { desc = BindW((s, alpha), (x, t)); loc = None }
let mkLambdaU ((x, a, ty), t) = { desc = LambdaU((x, a, ty), t); loc = None }
let mkCopyU s ((x, y), t) = { desc = CopyU(s, (x, y, t)); loc = None }
let mkHackU ty t = { desc = HackU(ty, t); loc = None }
let mkTypeAnnot t a = { desc = TypeAnnot(t, a); loc = None }

let rec is_value (term: t) : bool =
  match term.desc with
  | Var _ | ValW _ | UnitW -> true
  | InW((_,_,s), _) | FstW(s, _, _) | SndW(s, _, _) 
  | Select(_, _, s, _) -> is_value s
  | PairW((s, _), (t, _)) -> is_value s && is_value t
  | Case _ | ConstW _ | Box _ | Unbox _ | App _ | BindW _ 
  | HackU _ | ExternalU _ | CopyU _ | LambdaW _ | LambdaU _ 
  | TypeAnnot _ ->
    false

let rec is_pure (term: t) : bool =
  match term.desc with
  | Var _ | ValW _ | UnitW -> true
  | InW((_,_,s), _) | FstW(s, _, _) | SndW(s, _, _)
  | Select(_, _, s, _) -> is_pure s
  | PairW((s, _), (t, _)) -> is_pure s && is_pure t
  | Case(_, _, s, l) ->
    is_pure s && List.for_all l ~f:(fun (_, t) -> is_pure t)
  | App({desc = ConstW(Cintadd); _}, _, t) 
  | App({desc = ConstW(Cintsub); _}, _, t) 
  | App({desc = ConstW(Cintmul); _}, _, t) 
  | App({desc = ConstW(Cintdiv); _}, _, t) (* ? *)
  | App({desc = ConstW(Cinteq); _}, _, t)
  | App({desc = ConstW(Cintslt); _}, _, t) ->
    is_pure t
  | ConstW _ | Box _ | Unbox _ | App _ | BindW _ 
  | HackU _ | ExternalU _ | CopyU _ | LambdaW _ | LambdaU _ -> 
    false
  | TypeAnnot(t, _) ->
    is_pure t

let rec free_vars (term: t) : var list =
  let abs x l = List.filter l ~f:(fun z -> z <> x) in
  match term.desc with
  | Var(v) -> [v]
  | ValW _ | ConstW(_) | UnitW | ExternalU _ -> []
  | InW((_,_,s), _) | FstW(s, _, _) | SndW(s, _, _) 
  | Select(_, _, s, _) 
  | HackU(_, s) | Box(s, _) | Unbox(s, _) -> free_vars s
  | PairW((s, _), (t, _)) | App(s, _, t) -> 
    (free_vars s) @ (free_vars t)
  | CopyU(s, (x, y, t)) ->
    (free_vars s) @ (abs x (abs y (free_vars t)))
  | LambdaW((x, _), t) | LambdaU((x, _, _), t) ->
    abs x (free_vars t) 
  | BindW((s, _), (x, t)) ->
    (free_vars s) @ (abs x (free_vars t))
  | Case(_, _, s, l) ->
    free_vars s @ 
    List.fold_right l ~f:(fun (x, t) fv -> (abs x (free_vars t)) @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    free_vars t

let rec all_vars (term: t) : var list =
  match term.desc with
  | Var(v) -> [v]
  | ValW _ | ConstW(_) | UnitW | ExternalU _ -> []
  | InW((_,_,s), _) | FstW(s, _, _) | SndW(s, _, _) 
  | Select(_, _, s, _)
  | HackU(_, s) | Box(s, _) | Unbox(s, _) -> all_vars s
  | PairW((s, _), (t, _)) | App(s, _, t) 
  | CopyU(s, (_, _, t)) ->
    all_vars s @ all_vars t
  | LambdaW((x, _), t) | LambdaU((x, _, _), t) ->
    x :: all_vars t 
  | BindW((s, _), (x, t)) ->
    x :: all_vars s @ all_vars t
  | Case(_, _, s, l) ->
    all_vars s @ 
    List.fold_right l ~f:(fun (x, t) fv -> x :: all_vars t @ fv) ~init:[]
  | TypeAnnot(t, _) ->
    all_vars t

let rename_vars (f: var -> var) (term: t) : t =
  let rec rn term = 
    match term.desc with
    | Var(x) -> { term with desc = Var(f x) }
    | ValW _ | ConstW _  | UnitW | ExternalU _ ->
      term
    | InW((n, k, s), a) -> 
      { term with desc = InW((n, k, rn s), a) }
    | FstW(s, a, b) -> 
      { term with desc = FstW(rn s, a, b) }
    | SndW(s, a, b) -> 
      { term with desc = SndW(rn s, a, b) }
    | HackU(ty, s) -> 
      { term with desc = HackU(ty, rn s) }
    | Box(s, a) -> 
      { term with desc = Box(rn s, a) }
    | Unbox(s, a) -> 
      { term with desc = Unbox(rn s, a) }
    | PairW((s, a), (t, b)) -> 
      { term with desc = PairW((rn s, a), (rn t, b)) }
    | App(s, a, t) -> 
      { term with desc = App(rn s, a, rn t) }
    | CopyU(s, (x, y, t)) -> 
      { term with desc = CopyU(rn s, (f x, f y, rn t)) } 
    | LambdaW((x, ty), t) -> 
      { term with desc = LambdaW((f x, ty), rn t) } 
    | LambdaU((x, a, ty), t) -> 
      { term with desc = LambdaU((f x, a, ty), rn t) } 
    | BindW((s, a), (x, t)) -> 
      { term with desc = BindW((rn s, a), (f x, rn t)) }
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

(* substitues s for the head occurrence of x.
 * return None if t does not contain x.
*)
let head_subst (s: t) (x: var) (t: t) : t option =
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
      if x = y && (not !substituted) then 
        (substituted := true; s) (* substitute only once *)
      else 
        { term with desc = Var(apply sigma y) } 
    | UnitW | ValW _ | ConstW _ | ExternalU _ -> 
      term
    | InW((n, k, s), a) -> 
      {term with desc = InW((n, k, sub sigma s), a)}
    | FstW(s, a, b) -> 
      { term with desc = FstW(sub sigma s, a, b) }
    | SndW(s, a, b) -> 
      { term with desc = SndW(sub sigma s, a, b) }
    | HackU(ty, s) -> 
      {term with desc = HackU(ty, sub sigma s)}
    | Box(s, a) -> 
      { term with desc = Box(sub sigma s, a) }
    | Unbox(s, a) -> 
      { term with desc = Unbox(sub sigma s, a) }
    | PairW((s, a), (t, b)) -> 
      { term with desc = PairW((sub sigma s, a), (sub sigma t, b)) }
    | App (s, a, t) -> 
      { term with desc = App(sub sigma s, a, sub sigma t) }
    | CopyU(s, (x, y, t)) -> 
      { term with desc = CopyU(sub sigma s, abs2 sigma (x, y, t)) } 
    | LambdaW((x, ty), t) -> 
      let (x', t') = abs sigma (x, t) in
      { term with desc = LambdaW((x', ty), t') } 
    | LambdaU((x, a, ty), t) -> 
      let (x', t') = abs sigma (x, t) in
      { term with desc = LambdaU((x', a, ty), t') } 
    | BindW((s, a), (x, t)) -> 
      { term with desc = BindW((sub sigma s, a), abs sigma (x, t)) }
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

let subst (s: t) (x: var) (t: t) : t =
  (* rename x so that it is not free in s *)
  let fv = free_vars s @ (all_vars t) in
  let x' = variant_var_avoid x fv in
  let t' = if x = x' then t else rename_vars 
                                   (fun z -> if z = x then x' else z) t in
  let rec sub t = 
    match head_subst s x' t with
    | None -> t
    | Some t' -> sub t'
  in
  sub t'

(* Conveniencene function for n-ary let on WC level *)          
let let_tupleW (x: var) ((sigma: var list), (f: t)) : t =
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
       subst (mkSndW (mkVar z)) y
         (subst (mkFstW (mkVar z)) z1
            (let_tuple z1 (rest, f))) in
  let_tuple x (remove_shadow sigma, f)

let freshen_type_vars t =
  let new_type_vars = Int.Table.create () in
  let new_basetype_vars = Int.Table.create () in
  let fv x = 
    match Int.Table.find new_type_vars (Type.find x).id with
    | Some y -> y
    | None -> 
      let y = Type.newty Type.Var in
      Int.Table.replace new_type_vars ~key:(Type.find x).id ~data:y;
      y in
  let basefv x = 
    match Int.Table.find new_basetype_vars (Basetype.find x).id with
    | Some y -> y
    | None ->
      let y = Basetype.newty Basetype.Var in
      Int.Table.replace new_basetype_vars ~key:(Basetype.find x).id ~data:y;
      y in
  let f a = Type.subst fv basefv a in
  let fbase a = Basetype.subst basefv a in
  let rec mta term = 
    match term.desc with
    | Var(_) | UnitW -> term 
    | ValW(Cundef(a)) -> 
      { term with desc = ValW(Cundef(fbase a)) }
    | ConstW(Cpush(a)) -> 
      { term with desc = ConstW(Cpush(fbase a)) }
    | ConstW(Cpop(a)) ->
      { term with desc = ConstW(Cpop(fbase a)) }
    | ConstW(Ccall(s, a, b)) ->
      { term with desc = ConstW(Ccall(s, fbase a, fbase b)) }
    | ConstW(Cencode(a, b)) ->
      { term with desc = ConstW(Cencode(fbase a, fbase b)) }
    | ConstW(Cdecode(a, b)) ->
      { term with desc = ConstW(Cdecode(fbase a, fbase b)) }
    | ValW(Cintconst _) 
    | ConstW(Cintadd) 
    | ConstW(Cintsub)
    | ConstW(Cintmul) 
    | ConstW(Cintdiv) 
    | ConstW(Cinteq)
    | ConstW(Cintslt)
    | ConstW(Cintprint) 
    | ConstW(Cprint _) -> 
      term
    | InW((n, k, s), a) -> 
      { term with desc = InW((n, k, mta s), fbase a) }
    | FstW(s, a, b) -> 
      { term with desc = FstW(s, fbase a, fbase b) }
    | SndW(s, a, b) -> 
      { term with desc = SndW(s, fbase a, fbase b) }
    | Box(s, a) -> 
      { term with desc = Box(mta s, fbase a) }
    | Unbox(s, a) -> 
      { term with desc = Unbox(mta s, fbase a) }
    | PairW((s, a), (t, b)) -> 
      { term with desc = PairW((mta s, fbase a), (mta t, fbase b)) }
    | App(s, a, t) -> 
      { term with desc = App(mta s, f a, mta t) }
    | CopyU(s, (x, y, t)) -> 
      { term with desc = CopyU(mta s, (x, y, mta t)) } 
    | LambdaW((x, a), t) -> 
      { term with desc = LambdaW((x, fbase a), mta t) }
    | LambdaU((x, a, ty), t) -> 
      { term with desc = LambdaU((x, fbase a, f ty), mta t) } 
    | BindW((s, a), (x, t)) -> 
      { term with desc = BindW((mta s, fbase a), (x, mta t)) }
    | Select(id, params, s, i) -> 
      { term with desc = Select(id, List.map params ~f:fbase, mta s, i) }
    | Case(id, params, s, l) -> 
      { term with desc = Case(id, List.map params ~f:fbase, mta s, 
                              List.map l ~f:(fun (x, t) -> (x, mta t))) } 
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(mta t, f ty) }
    | HackU(ty, s) -> { term with desc = HackU(f ty, mta s) }
    | ExternalU(e, ty) -> { term with desc = ExternalU(e, f ty) }
  in mta t
