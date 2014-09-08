open Core.Std
open Unify
(* TODO: 
   - type checking
   - better printing
*)

module U = Unify(struct type t = unit end)

type label = { 
  name: int; 
  message_type: Basetype.t
}

type value =
  | Var of Term.var
  | Unit
  | Pair of value * value
  | In of (Basetype.Data.id * int * value) * Basetype.t
  | Fst of value * Basetype.t * Basetype.t
  | Snd of value * Basetype.t * Basetype.t
  | Select of value * (Basetype.Data.id * Basetype.t list) * int 
  | Undef of Basetype.t
  | IntConst of int
type term =
  | Val of value
  | Alloc of Basetype.t
  | Free of value * Basetype.t
  | Load of value * Basetype.t
  | Store of value * value * Basetype.t
  | Const of Term.op_const * value

let rec string_of_value v =
  match v with
  | Var(x) -> x
  | Unit -> "()"
  | Pair(v1, v2) -> 
    "(" ^ (string_of_value v1) ^ ", " ^ (string_of_value v2) ^ ")"
  | In((id, k, t), _) ->
    let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
    cname ^ "(" ^ string_of_value t ^ ") " (* ^ ") : " ^
    (Printing.string_of_basetype a) *)
  | Fst(t, _, _) -> string_of_value t ^ ".1" 
  | Snd(t, _, _) -> string_of_value t ^ ".2" 
  | Select(t, (id, params), i) ->
    let a = Basetype.newty (Basetype.DataW (id, params)) in 
    "select(" ^ string_of_value t ^ " : " ^
    (Printing.string_of_basetype a) ^ " )." 
    ^ (string_of_int i)
  | Undef(a) -> "undef(" ^ (Printing.string_of_basetype a) ^ ")"
  | IntConst(n) -> string_of_int n

let rec subst_value (rho: Term.var -> value) (v: value) =
  match v with
  | Var(x) -> rho x
  | Unit -> v
  | Pair(v1, v2) -> Pair(subst_value rho v1, subst_value rho v2)
  | In((id, i, v), a) -> In((id, i, subst_value rho v), a)
  | Fst(v, a, b) -> 
    begin 
      match subst_value rho v with
      | Pair(v1, _) -> v1 
      | w -> Fst(w, a, b)
    end
  | Snd(v, a, b) -> 
    begin 
      match subst_value rho v with
      | Pair(_, v2) -> v2 
      | w -> Snd(w, a, b)
    end
  | Select(v1, a, i) ->
    begin 
      match subst_value rho v1 with
      | In((_, j, w), a) -> 
        (* TODO: this is used in cbv.intml. Check that it's really ok.  *)
        if i=j then w else Undef(a)
      | w -> Select(w, a, i)
    end
  | Undef(a) -> Undef(a)
  | IntConst(i) -> IntConst(i)

let subst_term (rho: Term.var -> value) (t: term) =
  match t with
  | Val(v) -> Val(subst_value rho v)
  | Alloc(a) -> Alloc(a)
  | Free(v, a) -> Free(subst_value rho v, a)
  | Load(v, a) -> Load(subst_value rho v, a)
  | Store(v1, v2, a) -> Store(subst_value rho v1, subst_value rho v2, a)
  | Const(c, v) -> Const(c, subst_value rho v)


type let_binding =
  | Let of (Term.var * Basetype.t) * term
type let_bindings = let_binding list 

type block = 
    Unreachable of label
  | Direct of label * Term.var * let_bindings * value * label
  | InDirect of label * Term.var * let_bindings * value * (label list)
  | Branch of label * Term.var * let_bindings * 
              (Basetype.Data.id * Basetype.t list * value * 
               (Term.var * value * label) list)
  | Return of label * Term.var * let_bindings * value * Basetype.t

(** Invariant: Any block [b] in the list of blocks must 
    be reachable from the entry label by blocks appearing
    before [b] in the list of blocks. 
*)
type t = {
  func_name : string;
  entry_label : label;
  blocks : block list;
  return_type: Basetype.t;
}

let label_of_block (b : block) : label =
  match b with
  | Unreachable(l) 
  | Direct(l, _, _, _, _) 
  | InDirect(l, _, _ ,_ ,_)
  | Branch(l, _ , _, _) 
  | Return(l, _, _, _, _) -> l

let targets_of_block (b : block) : label list =
  match b with
  | Unreachable(_) -> []
  | Direct(_, _, _, _, l) -> [l]
  | InDirect(_, _, _ ,_ , ls) -> ls
  | Branch(_, _ , _, (_, _, _, cases)) -> List.map cases ~f:(fun (_, _, l) -> l)
  | Return(_, _, _, _, _) -> []

let check_blocks_invariant entry_label blocks =
  let defined_labels = Int.Table.create () in
  let invoked_labels = Int.Table.create () in
  Int.Table.replace invoked_labels ~key:entry_label.name ~data:();
  let check block =
    let l = label_of_block block in
    let ts = targets_of_block block in
    if Int.Table.mem defined_labels l.name then
      failwith ("ssa invariant: duplicate label definition");
    Int.Table.replace defined_labels ~key:l.name ~data:();
    if not (Int.Table.mem invoked_labels l.name) then
      failwith ("ssa invariant: no forward path from entry label");
    List.iter ts ~f:(fun l -> Int.Table.replace invoked_labels ~key:l.name ~data:()) in
  List.iter blocks ~f:check

let make 
      ~func_name:(func_name: string)
      ~entry_label:(entry_label: label) 
      ~blocks:(blocks: block list)
      ~return_type:(return_type: Basetype.t) =
  check_blocks_invariant entry_label blocks;
  { func_name = func_name;
    entry_label = entry_label;
    blocks = blocks;
    return_type = return_type }

(* TODO: NAMING! document naming assumptions *)

let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[]

let unTensorW a =
  match Basetype.finddesc a with
  | Basetype.TensorW(a1, a2) -> a1, a2
  | _ -> assert false

let defined_cases cases =
  let is_defined (_, (_, t)) =
    match t.Term.desc with 
    | Term.ValW(Term.Cundef _) -> false
    | _ -> true in
  List.mapi cases ~f:(fun i c -> i, c)
  |>  List.filter ~f:is_defined

let term_to_ssa (t: Term.t) 
  : let_bindings * value =
  (* Add type annotations in various places *)
  let rec to_ssa (t: Term.t) 
    : let_bindings * value =
    match t.Term.desc with
    | Term.Var(x) -> 
      [], Var(x)
    | Term.ValW(Term.Cundef a) ->
      [], Undef(a)
    | Term.ValW(Term.Cintconst(n)) ->
      [], IntConst(n)
    | Term.App({Term.desc = Term.ConstW(c); _}, a, arg) ->
      let retty =
        match Type.finddesc a with
        | Type.FunW(_, r) -> r
        | _ -> assert false in
      let x = fresh_var () in
      let ltarg, varg = to_ssa arg in
      Let((x, retty), Const(c, varg)) :: ltarg , Var(x)
    | Term.UnitW -> 
      [], Unit
    | Term.InW((id, j, t), a) -> 
      let lt, vt = to_ssa t in
      lt, In((id, j, vt), a)
    | Term.Box(t, a) -> 
      let lt, vt = to_ssa t in
      let addr = fresh_var () in
      let alloc = Let((addr, Basetype.newty (Basetype.NatW)), Alloc(a)) in
      let x = fresh_var () in
      let store = Let((x, Basetype.newty (Basetype.OneW)), 
                      Store(Var addr, vt, a)) in
      store :: alloc :: lt, Var(addr)
    | Term.Unbox(t, a) -> 
      let lt, vt = to_ssa t in
      let x = fresh_var () in
      let load = Let((x, a), Load(vt, a)) in
      let y = fresh_var () in
      let free = Let((y, Basetype.newty (Basetype.OneW)), Free(vt, a)) in
      free :: load :: lt, Var(x)
    | Term.PairW((t1, _), (t2, _)) ->
      let lt1, vt1 = to_ssa t1 in
      let lt2, vt2 = to_ssa t2 in
      lt2 @ lt1, Pair(vt1, vt2)
    | Term.FstW(t1, a, b) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Fst(v1, a, b)
    | Term.SndW(t1, a, b) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Snd(v1, a, b)
    | Term.BindW((t1, ax), (x, t2)) ->
      let lt1, v1 = to_ssa t1 in
      let x' = fresh_var () in
      let t2' = Term.subst (Term.mkVar x') x t2 in
      let lt2, v2 = to_ssa t2' in
      lt2 @ [Let((x', ax), Val v1)] @ lt1, v2
    | Term.Select(id, params, t1, i) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Select(v1, (id, params), i)
   | Term.Case(id, params, t1, cases) ->
      begin
        match defined_cases cases with
        | [(i, (y, {Term.desc = Term.Var z; _}))] when y = z->
          let lt1, v1 = to_ssa t1 in      
          let x = fresh_var () in
          let b = 
            let cons_types = Basetype.Data.constructor_types id params in
            assert (List.length cons_types > i);
            List.nth_exn cons_types i in
          [Let((x, b), Val(Select(v1, (id, params), i)))] @ lt1, Var x
        | _ -> 
          Printing.print_term t;
          failwith "illegal argument ssa (Case)"                 
      end
    | _ -> 
      Printing.print_term t;
      failwith "illegal argument ssa"
  in
  to_ssa t 

let circuit_to_ssa_body (name: string) (c: Circuit.t) : t =
  (* Supply of fresh variable names. 
   * (The instructions do not contain a free variable starting with "x")
  *)
  let open Term in
  let open Circuit in

  let blocks = ref [] in
  let emit_block block =
    blocks := block :: !blocks in

  let nodes_by_src = 
    let tbl = Int.Table.create () in
    let add_node n =
      List.iter (wires [n])
        ~f:(fun w -> Int.Table.replace tbl ~key:w.src ~data:n) in
    List.iter c.instructions ~f:add_node;
    tbl in
  let label_of_dst w = { name = w.dst; message_type = w.type_forward } in

  let make_block src dst =
    let z = fresh_var() in
    let sigma = Term.mkFstW (Term.mkVar z) in
    let m = Term.mkSndW (Term.mkVar z) in
    let to_ssa t target_type =
      (* TODO: all this type inference is quite inefficient *)
      let a = Typing.principal_typeW [(z, src.message_type)] [] t in
      U.unify a target_type;
      term_to_ssa t in
    if not (Hashtbl.mem nodes_by_src dst) then
      begin
        if dst = c.output.dst then
          let lt, v = to_ssa (Term.mkPairW sigma m) c.output.type_forward in
          Return(src, z, lt, v, c.output.type_forward)
        else 
          (* unreachable *)
          Unreachable(src)
      end
    else 
      match Int.Table.find_exn nodes_by_src dst with
      | Circuit.Axiom(w1 (* [f] *), (gamma, (y, f))) ->
        if dst = w1.src then
          let x = fresh_var () in
          (* ensure that variables in (y, f) do not collide with
             local name supply. *)
          let gamma = List.map gamma ~f:variant_var in
          let y = variant_var y in
          let f = variant f in
          let t1 = mkBindW m (y, f) in
          let t2 = mkBindW sigma (x, let_tupleW x (gamma, t1)) in
          let lt, vt = to_ssa (mkPairW sigma t2) w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else
          assert false
      | Circuit.Encode(w1) ->
        if dst = w1.src then
          let _, a = unTensorW w1.type_back in
          let _, b = unTensorW w1.type_forward in
          let lt, vt = 
            to_ssa (mkPairW sigma ((Circuit.embed a b m)))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.Decode(w1) ->
        if dst = w1.src then
          let _, a = unTensorW w1.type_back in
          let _, b = unTensorW w1.type_forward in
          let lt, vt = 
            to_ssa (mkPairW sigma ((Circuit.project b a m)))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.Tensor(w1, w2, w3) ->
        if dst = w1.src then
          (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
          let lt, vt = to_ssa (mkPairW sigma (mkInlW m)) w3.type_forward in
          Direct(src, z, lt, vt, label_of_dst w3)
        else if dst = w2.src then
          (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
          let lt, vt = to_ssa (mkPairW sigma (mkInrW m)) w3.type_forward in
          Direct(src, z, lt, vt, label_of_dst w3)
        else if dst = w3.src then
          (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
             <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)
          (* no additional type constraints needed; use variables *)
          let alpha = Basetype.newtyvar () in
          let beta1 = Basetype.newtyvar () in
          let beta2 = Basetype.newtyvar () in
          let beta = Basetype.newty (Basetype.DataW(Basetype.Data.sumid 2, 
                                                    [beta1; beta2])) in
          let lsigma, vsigma = to_ssa sigma alpha in
          let lm, vm = to_ssa m beta in
          let m' = fresh_var () in
          Branch(src, z, lm @ lsigma,
                 (Basetype.Data.sumid 2, 
                  [beta1; beta2],
                  vm, 
                  [(m', Pair(vsigma, Var(m')), label_of_dst w1);
                   (m', Pair(vsigma, Var(m')), label_of_dst w2)]))
        else assert false
      | Circuit.Der(w1 (* \Tens A X *), w2 (* X *), (gamma, f)) ->
        if dst = w1.src then
          let lt, vt = to_ssa (mkPairW sigma (mkSndW m)) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let gamma = List.map gamma ~f:variant_var in
          let f = variant f in
          let t = 
            let x = fresh_var () in
            mkPairW sigma 
              (mkPairW (mkBindW sigma (x, let_tupleW x (gamma, f))) m) in
          let lt, vt = to_ssa t w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Door(w1 (* X *), w2 (* \Tens A X *)) ->
        if dst = w1.src then
          let sigma' = mkFstW sigma in
          let c = mkSndW sigma in
          let lt, vt = 
            to_ssa (mkPairW sigma' (mkPairW c m)) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2) 
        else if dst = w2.src then
          let c = mkFstW m in
          let m' = mkSndW m in
          let lt, vt = 
            to_ssa (mkPairW (mkPairW sigma c) m') w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.Bind(w1 (* (\Tens A (1 => B))^* *), w2 (*  A => B *)) -> 
        if dst = w1.src then
          (* TODO: deconstruct A *)
          let b = mkSndW m in
          let lt, vt = to_ssa (mkPairW sigma b) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2) 
        else if
          dst = w2.src then
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW m mkUnitW)) w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.Assoc(w1 (* \Tens (A x B) X *), w2 (* \Tens A \Tens B X *)) ->
        if dst = w1.src then
          let cd = mkFstW m in
          let c = mkFstW cd in
          let d = mkSndW cd in
          let m' = mkSndW m in
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW c (mkPairW d m')))
              w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2) 
        else if dst = w2.src then
          let c = mkFstW m in
          let dm' = mkSndW m in
          let d = mkFstW dm' in
          let m' = mkSndW dm' in
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW (mkPairW c d) m')) 
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.LWeak(w1 (* \Tens A X *), 
                      w2 (* \Tens B X *)) (* B <= A *) ->
        if dst = w1.src then
          let _, a_token = unTensorW w1.type_back in
          let a, _ = unTensorW a_token in
          let _, b_token = unTensorW w2.type_forward in
          let b, _ = unTensorW b_token in
          let c = mkFstW m in
          let m' = mkSndW m in
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW (Circuit.project b a c) m'))
              w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2) 
        else if dst = w2.src then
          let _, a_token = unTensorW w1.type_forward in
          let a, _ = unTensorW a_token in
          let _, b_token = unTensorW w2.type_back in
          let b, _ = unTensorW b_token in
          let c = mkFstW m in
          let m' = mkSndW m in
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW (Circuit.embed b a c) m'))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else assert false
      | Circuit.Seq(w1 (* A=>B *), w2 (* B=>C *), w3 (* A=>C *)) ->
        if dst = w3.src then
          (*   <sigma, m> @ w3      |-->  <sigma, m> @ w1 *)
          Direct(src, z, [], Var z, label_of_dst w1) 
        else if dst = w1.src then
          (* <sigma, m> @ w1      |-->  <sigma, m> @ w2 *)
          Direct(src, z, [], Var z, label_of_dst w2) 
        else if dst = w2.src then
          (* <sigma, m> @ w2  |-->  <sigma, m> @ w3 *)
          Direct(src, z, [], Var z, label_of_dst w3) 
        else assert false
      | Circuit.Case(id, params, w1, ws) -> 
        assert (Basetype.Data.is_discriminated id);
        if List.mem (List.map ws ~f:(fun w -> w.src)) dst then
          (*  <sigma, <v,w>> @ w2         |-->  <sigma, <inl(v),w>> @ w1 *) 
          let rec find_src i ws =
            match ws with
            | [] -> assert false
            | w :: rest -> 
              if dst = w.src then i else find_src (i+1) rest in
          let i = find_src 0 ws in
          let c = mkFstW m in
          let m' = mkSndW m in
          let lt, vt = 
            to_ssa (mkPairW sigma (mkPairW (mkInW id i c) m'))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1) 
        else if dst = w1.src then
          (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
               <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
          let c = mkFstW m in
          let m' = mkSndW m in
          let alpha = Basetype.newtyvar () in
          let beta = Basetype.newtyvar () in
          let delta = Basetype.newtyvar () in
          let lsigma, vsigma = to_ssa sigma alpha in
          let lc, vc = to_ssa c beta in
          let lm', vm' = to_ssa m' delta in
          let y = fresh_var () in
          Branch(src, z, lm' @ lc @ lsigma, 
                 (id, params, vc, 
                  List.map ws
                    ~f:(fun w ->
                      (y, Pair(vsigma, Pair(Var(y), vm')), label_of_dst w))
                    ))
        else assert false
  in

  let generated_blocks = Int.Table.create () in
  let rec generate_blocks_from l =
    if l.name >= 0 && not (Int.Table.mem generated_blocks l.name) then
      let block = make_block l l.name in
      emit_block block;
      Int.Table.replace generated_blocks ~key:l.name ~data:();
      List.iter (targets_of_block block)
        ~f:generate_blocks_from in

  let entry_label = {name = c.output.src; 
                     message_type = c.output.type_back} in
  generate_blocks_from entry_label;
  make
    ~func_name: name
    ~entry_label: entry_label
    ~blocks: (List.rev !blocks)
    ~return_type: c.output.type_forward 

let add_entry_exit_code (f: t) : t =
  let sigma, arg_type = unTensorW f.entry_label.message_type in
  U.unify sigma (Basetype.newty Basetype.OneW);
  List.iter (Basetype.free_vars arg_type)
    ~f:(U.unify (Basetype.newty Basetype.NatW));
  let sigma, ret_type = unTensorW f.return_type in
  U.unify sigma (Basetype.newty Basetype.OneW);
  List.iter (Basetype.free_vars ret_type)
    ~f:(U.unify (Basetype.newty Basetype.NatW));

  let label_names = List.map f.blocks ~f:(fun b -> (label_of_block b).name) in
  let max_label_name = List.fold_right label_names ~f:max ~init:0 in

  let entry_label = {
    name = max_label_name + 1; 
    message_type = arg_type} in
  let entry_block = 
    let z = fresh_var() in
    Direct(entry_label, z, [], Pair(Unit, Var z), f.entry_label) in

  let exit_label = {
    name = max_label_name + 2; 
    message_type = ret_type} in
  let exit_block = 
    let z = fresh_var() in
    let v = Snd(Var z, Basetype.newty Basetype.OneW, ret_type) in 
    Return(exit_label, z, [], v, ret_type) in 

  let blocks' = 
    List.map f.blocks
      ~f:(fun b ->
        match b with
        | Return(src, x, lr, vr, _) -> Direct(src, x, lr, vr, exit_label)
        | b' -> b') in

  make
    ~func_name: f.func_name
    ~entry_label: entry_label
    ~blocks: (entry_block :: blocks' @ [exit_block])
    ~return_type: ret_type 

let circuit_to_ssa (name: string) (c: Circuit.t) : t =
  let body = circuit_to_ssa_body name c in
   add_entry_exit_code body 
   

(* TODO: proper printing *)


let string_of_term t =
  match t with
  | Val(v) -> "Val(" ^ (string_of_value v) ^ ")"
  | Alloc(a) -> 
    "Alloc(" ^ (Printing.string_of_basetype a) ^ ")"
  | Free(v1, a) -> 
    "Free(" ^ (string_of_value v1) ^ ", " ^
    (Printing.string_of_basetype a) ^ ")"
  | Load(v1, a) -> 
    "Load(" ^ (string_of_value v1) ^ ", " ^
    (Printing.string_of_basetype a) ^ ")"
  | Store(v1, v2, a) -> 
    "Store(" ^ (string_of_value v1) ^ ", " ^ (string_of_value v2) ^ ", " ^
    (Printing.string_of_basetype a) ^ ")"
  | Const(c, v) -> 
    (Printing.string_of_op_const c) ^ "(" ^ 
    (string_of_value v) ^ ")"

let string_of_letbndgs bndgs =
  String.concat ~sep:"" 
    (List.map (List.rev bndgs)
       ~f:(fun b -> match b with
         | Let((x, a), t) ->
           Printf.sprintf "   let %s: %s = %s\n" 
             x (Printing.string_of_basetype a) (string_of_term t))
    )

let string_of_block b =
  match b with
    | Unreachable(l) -> 
        Printf.sprintf " l%i(x : %s) = unreachable" 
          l.name 
          (Printing.string_of_basetype l.message_type)
    | Direct(l, x, bndgs, body, goal) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          l.name x (Printing.string_of_basetype l.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in l%i(%s) end\n" goal.name (string_of_value body))
    | InDirect(l, x, bndgs, body, goals) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          l.name x (Printing.string_of_basetype l.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in %s -> [%s] end\n" 
           (string_of_value body)
           (String.concat ~sep:"," 
              (List.map goals ~f:(fun l -> Printf.sprintf "l%i" l.name)))
        )
    | Branch(la, x, bndgs, (id, params, cond, cases)) ->
      let case_types = Basetype.Data.constructor_types id params in
        (Printf.sprintf " l%i(%s : %s) =\n" 
          la.name x (Printing.string_of_basetype la.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "    case %s of\n      | " (string_of_value cond)) ^
        (String.concat ~sep:"      | "
           (List.map 
              (List.zip_exn (List.zip_exn (Basetype.Data.constructor_names id) case_types) cases)
              ~f:(fun ((cname, _), (l, lb, lg)) ->
              Printf.sprintf "%s(%s) -> l%i(%s)\n" 
                cname (*(Printing.string_of_basetype a)*) l lg.name (string_of_value lb))
              
           ))
    | Return(l, x, bndgs, body, _) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          l.name x (Printing.string_of_basetype l.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in %s\n end\n" 
           (string_of_value body)
 (*           (Printing.string_of_type retty)*))

let string_of_func func =
  let buf = Buffer.create 80 in
    Buffer.add_string buf 
      (Printf.sprintf "%s(x : %s) : %s = l%i(x)\n\n"
         func.func_name
         (Printing.string_of_basetype func.entry_label.message_type)
         (Printing.string_of_basetype func.return_type)
         func.entry_label.name);
    List.iter func.blocks
      ~f:(fun block -> 
        Buffer.add_string buf (string_of_block block);
        Buffer.add_string buf "\n"
      );
  Buffer.contents buf

