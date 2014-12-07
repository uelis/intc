open Core.Std
open Unify

(********************
 * Values 
 ********************)

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
  | Const of Term.op_const * value
             
let rec fprint_value (oc: Out_channel.t) (v: value) : unit =
  match v with
  | Var(x) ->
    Printf.fprintf oc "%s" x
  | Unit -> 
    Printf.fprintf oc "()"
  | Pair(v1, v2) ->
    Out_channel.output_string oc "(";
    fprint_value oc v1;
    Out_channel.output_string oc ", ";
    fprint_value oc v2;
    Out_channel.output_string oc ")"
  | In((id, k, t), _) ->
    let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
    Out_channel.output_string oc cname;
    Out_channel.output_string oc "(";
    fprint_value oc t;
    Out_channel.output_string oc ")"
  | Fst(t, _, _) ->
    fprint_value oc t;
    Out_channel.output_string oc ".1"
  | Snd(t, _, _) ->
    fprint_value oc t;
    Out_channel.output_string oc ".2"
  | Select(t, _, i) ->
    Out_channel.output_string oc "select(";
    fprint_value oc t;
    Printf.fprintf oc ").%i" i
  | Undef(a) ->
    Out_channel.output_string oc "undef(";
    Out_channel.output_string oc (Printing.string_of_basetype a);
    Out_channel.output_string oc ")"
  | IntConst(n) -> 
    Printf.fprintf oc "%i" n

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
  | Const(c, v) -> Const(c, subst_value rho v)
                     
(********************
 * Programs 
 ********************)

type let_binding =
  | Let of (Term.var * Basetype.t) * term
type let_bindings = let_binding list
                      
type label = {
  name: int;
  message_type: Basetype.t
}

type block =
    Unreachable of label
  | Direct of label * Term.var * let_bindings * value * label
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
  | Branch(l, _ , _, _)
  | Return(l, _, _, _, _) -> l

let targets_of_block (b : block) : label list =
  match b with
  | Unreachable(_) -> []
  | Direct(_, _, _, _, l) -> [l]
  | Branch(_, _ , _, (_, _, _, cases)) -> List.map cases ~f:(fun (_, _, l) -> l)
  | Return(_, _, _, _, _) -> []

let fprint_term (oc: Out_channel.t) (t: term) : unit =
  match t with
  | Val(v) ->
    Out_channel.output_string oc "Val(";
    fprint_value oc v;
    Out_channel.output_string oc ")"
  | Const(c, v) ->
    Out_channel.output_string oc (Printing.string_of_op_const c);
    fprint_value oc v;
    Out_channel.output_string oc ")"

let fprint_letbndgs (oc: Out_channel.t) (bndgs: let_bindings) : unit =
  List.iter bndgs
    ~f:(function
      | Let((x, a), t) ->
        Printf.fprintf oc "   let %s = " x (* Printing.string_of_basetype a *);
        fprint_term oc t;
        Out_channel.output_string oc "\n"
    )

let fprint_block (oc: Out_channel.t) (b: block) : unit =
  match b with
    | Unreachable(l) ->
      Printf.fprintf oc " l%i(x : %s) = unreachable"
        l.name
        (Printing.string_of_basetype l.message_type)
    | Direct(l, x, bndgs, body, goal) ->
      Printf.fprintf oc " l%i(%s : %s) =\n" l.name x
        (Printing.string_of_basetype l.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   l%i(" goal.name;
      fprint_value oc body;
      Printf.fprintf oc ")\n"
    | Branch(la, x, bndgs, (id, params, cond, cases)) ->
      let constructor_names = Basetype.Data.constructor_names id in
      Printf.fprintf oc " l%i(%s : %s) =\n" la.name x
        (Printing.string_of_basetype la.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   case ";
      fprint_value oc cond;
      Printf.fprintf oc " of\n";
      List.iter2_exn constructor_names cases
        ~f:(fun cname (l, lb, lg) ->
          Printf.fprintf oc "   | %s(%s) -> l%i(" cname l lg.name;
          fprint_value oc lb;
          Printf.fprintf oc ")\n")
    | Return(l, x, bndgs, body, _) ->
      Printf.fprintf oc " l%i(%s : %s) =\n" l.name x
        (Printing.string_of_basetype l.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   return ";
      fprint_value oc body;
      Printf.fprintf oc "\n"

let fprint_func (oc: Out_channel.t) (func: t) : unit =
  Printf.fprintf oc "%s(x: %s) : %s = l%i(x)\n\n"
    func.func_name
    (Printing.string_of_basetype func.entry_label.message_type)
    (Printing.string_of_basetype func.return_type)
    (func.entry_label.name);
  List.iter func.blocks
    ~f:(fun block ->
      fprint_block oc block;
      Out_channel.output_string oc "\n")

(* The following functions verify the representation invariants and the
   types in ssa programs. *)
    
exception Type_error

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
    List.iter ts ~f:(fun l -> Int.Table.replace invoked_labels
                                ~key:l.name ~data:()) in
  List.iter blocks ~f:check

let rec typeof_value
          (gamma: Basetype.t Typing.context)
          (v: value)
  : Basetype.t =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else raise Type_error in
  match v with
  | Var(x) ->
    begin
      match List.Assoc.find gamma x with
      | Some b -> b
      | None -> raise Type_error
    end
  | Unit ->
    newty OneW
  | Pair(v1, v2) ->
    let a1 = typeof_value gamma v1 in
    let a2 = typeof_value gamma v2 in
    newty (TensorW(a1, a2))
  | In((id, n, v), a) ->
    let b = typeof_value gamma v in
    begin
      match finddesc a with
      | DataW(id', params) ->
        let constructor_types = Data.constructor_types id' params in
        if (id <> id') then raise Type_error;
        (match List.nth constructor_types n with
         | Some b' -> equals_exn b b'
         | None -> raise Type_error)
      | _ ->
        raise Type_error
    end;
    a
  | Fst(v, b1, b2) ->
    let a1 = typeof_value gamma v in
    equals_exn a1 (newty (TensorW(b1, b2)));
    b1
  | Snd(v, b1, b2) ->
    let a2 = typeof_value gamma v in
    equals_exn a2 (newty (TensorW(b1, b2)));
    b2
  | Select(v, (id, params), n) ->
    let a1 = typeof_value gamma v in
    let a = newty (DataW(id, params)) in
    equals_exn a a1;
    let constructor_types = Data.constructor_types id params in
    begin
      match List.nth constructor_types n with
      | Some b -> b
      | None -> raise Type_error
    end
  | Undef(a) ->
    a
  | IntConst(_) ->
    newty NatW
      
let typecheck_term
      (gamma: Basetype.t Typing.context)
      (t: term)
      (a: Basetype.t)
  : unit =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else raise Type_error in
  match t with
  | Val(v) ->
    let b = typeof_value gamma v in
    equals_exn a b
  | Const(Term.Cprint(_), v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty OneW);
    equals_exn a (newty OneW)
  | Const(Term.Cintadd, v) 
  | Const(Term.Cintsub, v)
  | Const(Term.Cintmul, v)
  | Const(Term.Cintdiv, v) ->
    let b = typeof_value gamma v in
    let intty = newty NatW in
    equals_exn b (newty (TensorW(intty, intty)));
    equals_exn a intty
  | Const(Term.Cinteq, v)
  | Const(Term.Cintslt, v) ->
    let b = typeof_value gamma v in
    let intty = newty NatW in
    let boolty = Basetype.newty (Basetype.DataW(Basetype.Data.boolid, [])) in
    equals_exn b (newty (TensorW(intty, intty)));
    equals_exn a boolty
  | Const(Term.Cintprint, v) ->
    let b = typeof_value gamma v in
    let intty = newty NatW in
    equals_exn b intty;
    equals_exn a (newty OneW)
  | Const(Term.Calloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty OneW);
    equals_exn a (newty (BoxW b))
  | Const(Term.Cfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxW b));
    equals_exn a (newty OneW)
  | Const(Term.Cload(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxW b));
    equals_exn a b
  | Const(Term.Cstore(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (TensorW(newty (BoxW b), b)));
    equals_exn a (newty OneW)
  | Const(Term.Cpush(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c b;
    equals_exn a (newty OneW)
  | Const(Term.Cpop(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty OneW);
    equals_exn a b
  | Const(Term.Ccall(_, b1, b2), v)
  | Const(Term.Cencode(b1, b2), v) 
  | Const(Term.Cdecode(b1, b2), v) ->
    let c = typeof_value gamma v in
    equals_exn c b1;
    equals_exn a b2

let rec typecheck_let_bindings
      (gamma: Basetype.t Typing.context)
      (l: let_bindings)
  : Basetype.t Typing.context =
  match l with
  | [] ->
    gamma 
  | Let((v, a), t) :: ls ->
    let gamma1 = typecheck_let_bindings gamma ls in
    typecheck_term gamma1 t a;
    (v, a) :: gamma1

let typecheck_block (label_types: Basetype.t Int.Table.t) (b: block) : unit =
  let equals_exn a b =
    if Basetype.equals a b then () else raise Type_error in
  let check_label_exn l a =
    match Int.Table.find label_types l.name with
    | Some b -> equals_exn l.message_type b
    | None -> raise Type_error in
  match b with
  | Unreachable(_) -> ()
  | Direct(s, x, l, v, d) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let a = typeof_value gamma v in
    equals_exn a (d.message_type);
  | Branch(s, x, l, (id, params, v, ds)) ->
    let constructor_types = Basetype.Data.constructor_types id params in
    let bs = List.zip ds constructor_types in
    begin
      match bs with
      | Some bs ->
        let gamma0 = [(x, s.message_type)] in
        let gamma = typecheck_let_bindings gamma0 l in
        let va = typeof_value gamma v in
        equals_exn va (Basetype.newty
                         (Basetype.DataW(id, params)));
        List.iter bs
          ~f:(fun ((x, v, d), a) ->
            let b = typeof_value ((x, a) :: gamma) v in
            check_label_exn d b)
      | None ->
        raise Type_error
    end
  | Return(s, x, l, v, a) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let b = typeof_value gamma v in
    equals_exn a b

let typechecks (blocks: block list) : bool =
  try
    let label_types = Int.Table.create () in
    List.iter blocks ~f:(fun b ->
      let l = label_of_block b in
      match Int.Table.add label_types ~key:l.name ~data:l.message_type with
      | `Duplicate -> raise Type_error
      | `Ok -> ()
    );
    List.iter blocks ~f:(typecheck_block label_types);
    true
  with
  | Type_error -> false
    

let make ~func_name:(func_name: string)
      ~entry_label:(entry_label: label)
      ~blocks:(blocks: block list)
      ~return_type:(return_type: Basetype.t) =
  check_blocks_invariant entry_label blocks;
  assert (typechecks blocks);
  { func_name = func_name;
    entry_label = entry_label;
    blocks = blocks;
    return_type = return_type }


(****************************
 * Translation from circuits
 ****************************)
    
(* INVARIANT: The supply of fresh names in the
 * generation of ssa programs has the form x0, x1, ...
 * This means that only source terms not containing
 * variables of this form should be translated. *)
let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[]

let unTensorW a =
  match Basetype.finddesc a with
  | Basetype.TensorW(a1, a2) -> a1, a2
  | _ -> assert false

let term_value_to_ssa (t: Term.t)
  : let_bindings * value =
  (* Add type annotations in various places *)
  let rec to_ssa (t: Term.t)
    : let_bindings * value =
    match t.Term.desc with
    | Term.Var(x) ->
      [], Var(x)
    | Term.ConstV(Term.Cundef a) ->
      [], Undef(a)
    | Term.ConstV(Term.Cintconst(n)) ->
      [], IntConst(n)
    | Term.UnitV ->
      [], Unit
    | Term.InV((id, j, t), a) ->
      let lt, vt = to_ssa t in
      lt, In((id, j, vt), a)
    | Term.PairV((t1, _), (t2, _)) ->
      let lt1, vt1 = to_ssa t1 in
      let lt2, vt2 = to_ssa t2 in
      lt2 @ lt1, Pair(vt1, vt2)
    | Term.FstV(t1, a, b) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Fst(v1, a, b)
    | Term.SndV(t1, a, b) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Snd(v1, a, b)
    | Term.Bind((t1, ax), (x, t2)) ->
      let lt1, v1 = to_ssa t1 in
      let x' = fresh_var () in
      let t2' = Term.subst (Term.mkVar x') x t2 in
      let lt2, v2 = to_ssa t2' in
      lt2 @ [Let((x', ax), Val v1)] @ lt1, v2
    | Term.Select(id, params, t1, i) ->
      let lt1, v1 = to_ssa t1 in
      lt1, Select(v1, (id, params), i)
    | _ ->
      Printing.print_term t;
      failwith "illegal argument val ssa"
  in
  to_ssa t

let term_to_ssa (t: Term.t)
  : let_bindings * value =
  (* Add type annotations in various places *)
  let rec to_ssa (t: Term.t)
    : let_bindings * value =
    match t.Term.desc with
    | Term.Return(t1, a) ->
      let lt1, v1 = term_value_to_ssa t1 in
      let x = fresh_var () in
      [Let((x, a), Val v1)] @ lt1, Var x
    | Term.Bind((t1, ax), (x, t2)) ->
      let lt1, v1 = to_ssa t1 in
      let x' = fresh_var () in
      let t2' = Term.subst (Term.mkVar x') x t2 in
      let lt2, v2 = to_ssa t2' in
      lt2 @ [Let((x', ax), Val v1)] @ lt1, v2
    | Term.App({Term.desc = Term.Const(c); _}, a, arg) ->
      let retty =
        match Type.finddesc a with
        | Type.FunW(_, r) ->
          begin
            match Type.finddesc r with
            | Type.Base(ar) -> ar
            | _ -> assert false
          end
        | _ -> assert false in
      let x = fresh_var () in
      let ltarg, varg = term_value_to_ssa arg in
      Let((x, retty), Const(c, varg)) :: ltarg , Var(x)
    | _ ->
      Printing.print_term t;
      failwith "illegal argument ssa"
  in
  to_ssa t
    
module U = Unify(struct type t = unit end)

(* TODO: This implementation is quite inefficient with many uses of type
 * inference. The types are all known and could be constructed directly. *)
let circuit_to_ssa_body (name: string) (c: Circuit.t) : t =
  (* Notice that the freshness invariant must be considered here:
   * The instructions do not contain a free variable starting with "x". *)
  let open Circuit in

  let blocks = ref [] in
  let emit_block block =
    blocks := block :: !blocks in

  let nodes_by_src =
    let tbl = Int.Table.create () in
    let add_node n =
      List.iter (wires n)
        ~f:(fun w -> Int.Table.replace tbl ~key:w.src ~data:n) in
    List.iter c.instructions ~f:add_node;
    tbl in
  let label_of_dst w = { name = w.dst; message_type = w.type_forward } in

  let make_block src dst =
    let z = fresh_var() in
    let sigma = Term.mkReturn (Term.mkFstV (Term.mkVar z)) in
    let m = Term.mkReturn (Term.mkSndV (Term.mkVar z)) in
    let (>>=) t f =
      let open Term in
      let z1 = fresh_var () in
      mkBind t
        (z1, mkReturn (f (mkVar z1))) in
    let mkFst t1 =
      let open Term in
      let z1 = fresh_var () in
      mkBind t1
        (z1, mkReturn (mkFstV (mkVar z1))) in
    let mkSnd t1 =
      let open Term in
      let z1 = fresh_var () in
      mkBind t1
        (z1, mkReturn (mkSndV (mkVar z1))) in
    let mkPair t1 t2 =
      let open Term in
      let z1 = fresh_var () in
      let z2 = fresh_var () in
      mkBind t1
        (z1, mkBind t2
               (z2, mkReturn (mkPairV (mkVar z1) (mkVar z2)))) in
    let to_ssa t target_type =
      let a = Typing.principal_type [(z, src.message_type)] [] t in
      U.unify_eqs [U.Type_eq(a, (Type.newty (Type.Base target_type)), None)];
      begin
        match Type.finddesc a with
        | Type.Base a0 -> U.unify a0 target_type
        | _ -> assert false
      end;
      term_to_ssa t in
    if not (Hashtbl.mem nodes_by_src dst) then
      begin
        if dst = c.output.dst then
          let lt, v = to_ssa (mkPair sigma m) c.output.type_forward in
          Return(src, z, lt, v, c.output.type_forward)
        else
          (* unreachable *)
          Unreachable(src)
      end
    else
      let open Term in
      match Int.Table.find_exn nodes_by_src dst with
      | Circuit.Base(w1 (* [f] *), (gamma, f)) ->
        if dst = w1.src then
          let x = fresh_var () in
          (* ensure that variables in (y, f) do not collide with
             local name supply. *)
          let gamma = List.map gamma ~f:variant_var in
          let t = variant f in
          let t1 = mkBind sigma (x, let_tupleW x (gamma, t)) in
          let lt, vt = to_ssa (mkPair sigma t1) w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else
          assert false
      | Circuit.Encode(w1) ->
        if dst = w1.src then
          let _, a = unTensorW w1.type_back in
          let _, b = unTensorW w1.type_forward in
          let lt, vt =
            to_ssa (mkPair sigma ((Circuit.embed a b m)))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Decode(w1) ->
        if dst = w1.src then
          let _, a = unTensorW w1.type_back in
          let _, b = unTensorW w1.type_forward in
          let lt, vt =
            to_ssa (mkPair sigma ((Circuit.project b a m)))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Tensor(w1, w2, w3) ->
        if dst = w1.src then
          (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
          let lt, vt = to_ssa (mkPair sigma (m >>= mkInlV)) w3.type_forward in
          Direct(src, z, lt, vt, label_of_dst w3)
        else if dst = w2.src then
          (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
          let lt, vt = to_ssa (mkPair sigma (m >>= mkInrV)) w3.type_forward in
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
          let lt, vt = to_ssa (mkPair sigma (mkSnd m)) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let gamma = List.map gamma ~f:variant_var in
          let f = variant f in
          let t =
            let x = fresh_var () in
            mkPair sigma
              (mkPair (mkBind sigma (x, let_tupleW x (gamma, mkReturn f))) m) in
          let lt, vt = to_ssa t w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.App(w1 (* (A => X) *), (gamma, f), w2 (* X *)) ->
        if dst = w1.src then
          let lt, vt = to_ssa (mkPair sigma m) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let gamma = List.map gamma ~f:variant_var in
          let f = variant f in
          let t =
            let x = fresh_var () in
            mkPair sigma
              (mkPair (mkBind sigma (x, let_tupleW x (gamma, mkReturn f))) m) in
          let lt, vt = to_ssa t w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Door(w1 (* X *), w2 (* \Tens A X *)) ->
        if dst = w1.src then
          let sigma' = mkFst sigma in
          let c = mkSnd sigma in
          let lt, vt =
            to_ssa (mkPair sigma' (mkPair c m)) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let c = mkFst m in
          let m' = mkSnd m in
          let lt, vt =
            to_ssa (mkPair (mkPair sigma c) m') w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Bind(w1 (* \Tens A X *), w2 (*  A => X *)) ->
        if dst = w1.src then
          (* TODO: deconstruct A *)
          let b = mkSnd m in
          let lt, vt = to_ssa (mkPair sigma b) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let lt, vt =
            to_ssa (mkPair sigma m) w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Assoc(w1 (* \Tens (A x B) X *), w2 (* \Tens A \Tens B X *)) ->
        if dst = w1.src then
          let cd = mkFst m in
          let c = mkFst cd in
          let d = mkSnd cd in
          let m' = mkSnd m in
          let lt, vt =
            to_ssa (mkPair sigma (mkPair c (mkPair d m')))
              w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let c = mkFst m in
          let dm' = mkSnd m in
          let d = mkFst dm' in
          let m' = mkSnd dm' in
          let lt, vt =
            to_ssa (mkPair sigma (mkPair (mkPair c d) m'))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Direct(w1 (* (X- => TX+)^* *), w2 (* X *)) ->
        if dst = w1.src then
          let lt, vt = to_ssa (mkPair sigma m) w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let lt, vt =
            to_ssa (mkPair sigma (mkPair m (mkReturn mkUnitV)))
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
          let c = mkFst m in
          let m' = mkSnd m in
          let lt, vt =
            to_ssa (mkPair sigma (mkPair (Circuit.project b a c) m'))
              w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          let _, a_token = unTensorW w1.type_forward in
          let a, _ = unTensorW a_token in
          let _, b_token = unTensorW w2.type_back in
          let b, _ = unTensorW b_token in
          let c = mkFst m in
          let m' = mkSnd m in
          let lt, vt =
            to_ssa (mkPair sigma (mkPair (Circuit.embed b a c) m'))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Seq(w1 (* TA^* *), w2 (* \Tensor A TB^* *), w3 (* TB *)) ->
        if dst = w3.src then
          (*   <sigma, m> @ w3      |-->  <sigma, m> @ w1 *)
          Direct(src, z, [], Var z, label_of_dst w1)
        else if dst = w1.src then
          (* <sigma, m> @ w1      |-->  <sigma, m> @ w2 *)
          let lt, vt =
            to_ssa (mkPair sigma (mkPair m (mkReturn mkUnitV)))
              w2.type_forward in
          Direct(src, z, lt, vt, label_of_dst w2)
        else if dst = w2.src then
          (* <sigma, m> @ w2  |-->  <sigma, m> @ w3 *)
          let lt, vt =
            to_ssa (mkPair sigma (mkSnd m))
              w3.type_forward in
          Direct(src, z, lt, vt, label_of_dst w3)
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
          let c = mkFst m in
          let m' = mkSnd m in
          let t1 =
            let x = fresh_var () in
            mkBind c (x, mkReturn (mkInV id i (mkVar x))) in
          let lt, vt =
            to_ssa (mkPair sigma (mkPair t1 m'))
              w1.type_forward in
          Direct(src, z, lt, vt, label_of_dst w1)
        else if dst = w1.src then
          (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
               <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
          let c = mkFst m in
          let m' = mkSnd m in
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
    message_type =
      Basetype.newty (
        Basetype.TensorW(
          Basetype.newty Basetype.OneW,
          ret_type))
  } in
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
  let p = add_entry_exit_code body in
  p
