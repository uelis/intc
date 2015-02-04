open Core.Std

(********************
 * Values
 ********************)

type value =
  | Var of Ident.t
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
  | Const of Ast.op_const * value

let rec fprint_value (oc: Out_channel.t) (v: value) : unit =
  match v with
  | Var(x) ->
    Printf.fprintf oc "%s" (Ident.to_string x)
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

let rec subst_value (rho: Ident.t -> value) (v: value) =
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
        (* TODO: this is used in cbv.intml. Check that it's really ok. *)
        if i=j then w else
          (* undefined *)
          let ai =
            match Basetype.case a with
            | Basetype.Sgn (Basetype.DataB(id, params)) ->
              begin
                match List.nth (Basetype.Data.constructor_types id params) i with
                | Some b -> b
                | None -> assert false
              end
            | _ -> assert false in
          Undef(ai)
      | w -> Select(w, a, i)
    end
  | Undef(a) -> Undef(a)
  | IntConst(i) -> IntConst(i)

let subst_term (rho: Ident.t -> value) (t: term) =
  match t with
  | Val(v) -> Val(subst_value rho v)
  | Const(c, v) -> Const(c, subst_value rho v)

(********************
 * Programs
 ********************)

type let_binding =
  | Let of (Ident.t * Basetype.t) * term
type let_bindings = let_binding list

type label = {
  name: int;
  message_type: Basetype.t
}

type block =
    Unreachable of label
  | Direct of label * Ident.t * let_bindings * value * label
  | Branch of label * Ident.t * let_bindings *
              (Basetype.Data.id * Basetype.t list * value *
               (Ident.t * value * label) list)
  | Return of label * Ident.t * let_bindings * value * Basetype.t

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
    Out_channel.output_string oc "(";
    fprint_value oc v;
    Out_channel.output_string oc ")"

let fprint_letbndgs (oc: Out_channel.t) (bndgs: let_bindings) : unit =
  List.iter (List.rev bndgs)
    ~f:(function
      | Let((x, _), t) ->
        Printf.fprintf oc "   let %s = " (Ident.to_string x);
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
      Printf.fprintf oc " l%i(%s : %s) =\n" l.name (Ident.to_string x)
        (Printing.string_of_basetype l.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   l%i(" goal.name;
      fprint_value oc body;
      Printf.fprintf oc ")\n"
    | Branch(la, x, bndgs, (id, _, cond, cases)) ->
      let constructor_names = Basetype.Data.constructor_names id in
      Printf.fprintf oc " l%i(%s : %s) =\n" la.name (Ident.to_string x)
        (Printing.string_of_basetype la.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   case ";
      fprint_value oc cond;
      Printf.fprintf oc " of\n";
      List.iter2_exn constructor_names cases
        ~f:(fun cname (l, lb, lg) ->
          Printf.fprintf oc "   | %s(%s) -> l%i(" cname (Ident.to_string l) lg.name;
          fprint_value oc lb;
          Printf.fprintf oc ")\n")
    | Return(l, x, bndgs, body, _) ->
      Printf.fprintf oc " l%i(%s : %s) =\n" l.name (Ident.to_string x)
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
    if equals a b then () else failwith "internal ssa.ml: type error" in
  match v with
  | Var(x) ->
    begin
      match List.Assoc.find gamma x with
      | Some b -> b
      | None -> failwith ("internal ssa.ml: undefined variable " ^ (Ident.to_string x))
    end
  | Unit ->
    newty UnitB
  | Pair(v1, v2) ->
    let a1 = typeof_value gamma v1 in
    let a2 = typeof_value gamma v2 in
    newty (PairB(a1, a2))
  | In((id, n, v), a) ->
    let b = typeof_value gamma v in
    begin
      match case a with
      | Sgn (DataB(id', params)) ->
        let constructor_types = Data.constructor_types id' params in
        if (id <> id') then failwith "internal ssa.ml: wrong data type";
        (match List.nth constructor_types n with
         | Some b' -> equals_exn b b'
         | None -> failwith "internal ssa.ml: wrong constructor type")
      | _ ->
        fprint_value stderr v;
        failwith "internal ssa.ml: data type expected"
    end;
    a
  | Fst(v, b1, b2) ->
    let a1 = typeof_value gamma v in
    equals_exn a1 (newty (PairB(b1, b2)));
    b1
  | Snd(v, b1, b2) ->
    let a2 = typeof_value gamma v in
    equals_exn a2 (newty (PairB(b1, b2)));
    b2
  | Select(v, (id, params), n) ->
    let a1 = typeof_value gamma v in
    let a = newty (DataB(id, params)) in
    equals_exn a a1;
    let constructor_types = Data.constructor_types id params in
    begin
      match List.nth constructor_types n with
      | Some b -> b
      | None ->
        failwith "internal ssa.ml: unknown constructor"
    end
  | Undef(a) ->
    a
  | IntConst(_) ->
    newty IntB

let typecheck_term
      (gamma: Basetype.t Typing.context)
      (t: term)
      (a: Basetype.t)
  : unit =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else failwith "internal ssa.ml: type mismatch" in
  match t with
  | Val(v) ->
    let b = typeof_value gamma v in
    equals_exn a b
  | Const(Ast.Cprint(_), v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty UnitB);
    equals_exn a (newty UnitB)
  | Const(Ast.Cintadd, v)
  | Const(Ast.Cintsub, v)
  | Const(Ast.Cintmul, v)
  | Const(Ast.Cintdiv, v)
  | Const(Ast.Cintshl, v)
  | Const(Ast.Cintshr, v)
  | Const(Ast.Cintsar, v)
  | Const(Ast.Cintand, v)
  | Const(Ast.Cintor, v)
  | Const(Ast.Cintxor, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    equals_exn b (newty (PairB(intty, intty)));
    equals_exn a intty
  | Const(Ast.Cinteq, v)
  | Const(Ast.Cintlt, v)
  | Const(Ast.Cintslt, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    let boolty = Basetype.newty (Basetype.DataB(Basetype.Data.boolid, [])) in
    equals_exn b (newty (PairB(intty, intty)));
    equals_exn a boolty
  | Const(Ast.Cintprint, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    equals_exn b intty;
    equals_exn a (newty UnitB)
  | Const(Ast.Calloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty UnitB);
    equals_exn a (newty (BoxB b))
  | Const(Ast.Cfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    equals_exn a (newty UnitB)
  | Const(Ast.Cload(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    equals_exn a b
  | Const(Ast.Cstore(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (PairB(newty (BoxB b), b)));
    equals_exn a (newty UnitB)
  | Const(Ast.Carrayalloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty IntB);
    equals_exn a (newty (ArrayB b))
  | Const(Ast.Carrayfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (ArrayB b));
    equals_exn a (newty UnitB)
  | Const(Ast.Carrayget(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (PairB(newty (ArrayB b), newty IntB)));
    equals_exn a (newty (BoxB(b)))
  | Const(Ast.Cpush(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c b;
    equals_exn a (newty UnitB)
  | Const(Ast.Cpop(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty UnitB);
    equals_exn a b
  | Const(Ast.Ccall(_, b1, b2), v) ->
    let c = typeof_value gamma v in
    equals_exn c b1;
    equals_exn a b2
  | Const(Ast.Cencode b, v) ->
    let c = typeof_value gamma v in
    equals_exn b c
  | Const(Ast.Cdecode b, v) ->
    equals_exn b a

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
    if Basetype.equals a b then () else failwith "internal ssa.ml: type mismatch" in
  let check_label_exn l a =
    match Int.Table.find label_types l.name with
    | Some b ->
      equals_exn a b;
      equals_exn l.message_type b
    | None -> failwith "internal ssa.ml: wrong argument in jump" in
  match b with
  | Unreachable(_) -> ()
  | Direct(s, x, l, v, d) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let a = typeof_value gamma v in
    check_label_exn d a
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
                         (Basetype.DataB(id, params)));
        List.iter bs
          ~f:(fun ((x, v, d), a) ->
            let b = typeof_value ((x, a) :: gamma) v in
            check_label_exn d b)
      | None ->
        failwith "internal ssa.ml: wrong number of cases in branch"
    end
  | Return(s, x, l, v, a) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let b = typeof_value gamma v in
    equals_exn a b

let typecheck (blocks: block list) : unit =
  let label_types = Int.Table.create () in
  List.iter blocks ~f:(fun b ->
    let l = label_of_block b in
    match Int.Table.add label_types ~key:l.name ~data:l.message_type with
    | `Duplicate -> failwith "internal ssa.ml: duplicte block"
    | `Ok -> ()
  );
  List.iter blocks ~f:(typecheck_block label_types)


let make ~func_name:(func_name: string)
      ~entry_label:(entry_label: label)
      ~blocks:(blocks: block list)
      ~return_type:(return_type: Basetype.t) =
  assert (check_blocks_invariant entry_label blocks = ());
  assert (typecheck blocks = ()); (* execute for effect *)
  { func_name = func_name;
    entry_label = entry_label;
    blocks = blocks;
    return_type = return_type }


(****************************
 * Translation from circuits
 ****************************)

let unPairB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.PairB(a1, a2)) -> a1, a2
  | _ -> assert false

let unSumB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.DataB(id, params)) ->
    begin
      assert (id = Basetype.Data.sumid 2);
      match params with
      | [a1; a2] -> a1, a2
      | _ -> assert false
    end
  | _ -> assert false

let inl a v =
  let id = Basetype.Data.sumid 2 in
  In((id, 0, v), a)

let inr a v =
  let id = Basetype.Data.sumid 2 in
  In((id, 1, v), a)

let rec term_value_to_ssa (t: Typedterm.value) : let_bindings * value =
  match t.Typedterm.value_desc with
  | Typedterm.VarV(x) ->
    [], Var(x)
  | Typedterm.ConstV(Ast.Cundef a) ->
    [], Undef(a)
  | Typedterm.ConstV(Ast.Cintconst(n)) ->
    [], IntConst(n)
  | Typedterm.UnitV ->
    [], Unit
  | Typedterm.InV(id, j, t1) ->
    let lt, vt = term_value_to_ssa t1 in
    let a = t.Typedterm.value_type in
    lt, In((id, j, vt), a)
  | Typedterm.PairV(t1, t2) ->
    let lt1, vt1 = term_value_to_ssa t1 in
    let lt2, vt2 = term_value_to_ssa t2 in
    lt2 @ lt1, Pair(vt1, vt2)
  | Typedterm.FstV(t1) ->
    let lt1, v1 = term_value_to_ssa t1 in
    let a, b =
      match Basetype.case t1.Typedterm.value_type with
      | Basetype.Sgn (Basetype.PairB(a, b)) -> a, b
      | _ -> assert false in
    lt1, Fst(v1, a, b)
  | Typedterm.SndV(t1) ->
    let lt1, v1 = term_value_to_ssa t1 in
    let a, b =
      match Basetype.case t1.Typedterm.value_type with
      | Basetype.Sgn (Basetype.PairB(a, b)) -> a, b
      | _ -> assert false in
    lt1, Snd(v1, a, b)
  | Typedterm.SelectV(id, params, t1, i) ->
    let lt1, v1 = term_value_to_ssa t1 in
    lt1, Select(v1, (id, params), i)

let rec term_to_ssa (t: Typedterm.t) : let_bindings * value =
  match t.Typedterm.t_desc with
  | Typedterm.Return(t1) ->
    let lt1, v1 = term_value_to_ssa t1 in
    let x = Ident.fresh "x" in
    let a = t1.Typedterm.value_type in
    [Let((x, a), Val v1)] @ lt1, Var x
  | Typedterm.Bind((t1, ax), (x, t2)) ->
    let lt1, v1 = term_to_ssa t1 in
    let lt2, v2 = term_to_ssa t2 in
    lt2 @ [Let((x, ax), Val v1)] @ lt1, v2
  | Typedterm.AppV({ Typedterm.t_desc = Typedterm.Const(c);
                     Typedterm.t_type = a;
                     _},
                   arg) ->
    let retty =
      match Type.case a with
      | Type.Sgn (Type.FunV(_, r)) ->
        begin
          match Type.case r with
          | Type.Sgn(Type.Base(ar)) -> ar
          | _ -> assert false
        end
      | _ -> assert false in
    let x = Ident.fresh "x" in
    let ltarg, varg = term_value_to_ssa arg in
    Let((x, retty), Const(c, varg)) :: ltarg , Var(x)
  | _ ->
    failwith "illegal argument ssa"

let rec bind_context z a (gamma: Basetype.t Typing.context) : let_binding list =
  match gamma with
  | [] -> []
  | (x, b) :: rest ->
    let arest =
      match Basetype.case a with
      | Basetype.Sgn (Basetype.PairB(arest, ax)) ->
        assert (Basetype.equals b ax);
        arest
      | _ -> assert false in
    Let((x, b), Val(Snd(z, arest, b))) ::
    bind_context (Fst(z, arest, b)) arest rest

let circuit_to_ssa_body (name: string) (c: Circuit.t) : t =
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
    let z = Ident.fresh "z" in
    let sigma_type, m_type = unPairB src.message_type in
    let sigma_val = Fst(Var z, sigma_type, m_type) in
    let m_val = Snd(Var z, sigma_type, m_type) in

    if not (Hashtbl.mem nodes_by_src dst) then
      begin
        if dst = c.output.dst then
          Return(src, z, [], Var(z), c.output.type_forward)
        else
          (* unreachable *)
          Unreachable(src)
      end
    else
      match Int.Table.find_exn nodes_by_src dst with
      | Circuit.Base(w1 (* [f] *), (gamma, f)) ->
        if dst = w1.src then
          (* ensure that variables in (y, f) do not collide with
             local name supply. *)
          let ltgamma = bind_context sigma_val sigma_type gamma in
          let lt, m' = term_to_ssa f in
          let vt = Pair(sigma_val, m') in
          Direct(src, z, lt @ ltgamma, vt, label_of_dst w1)
        else
          assert false
      | Circuit.Encode(w1) ->
        if dst = w1.src then
          let a, _ = unPairB m_type in
          let m_term = Ast.mkReturn (Ast.mkFstV (Ast.mkSndV (Ast.mkVar z))) in
          let _, b = unPairB w1.type_forward in
          let embed = Typing.check_term [(z, src.message_type)] []
                        (Ast.mkTypeAnnot
                           (Circuit.embed a b m_term)
                           (Type.newty (Type.Base b))) in
          let lt, r = term_to_ssa embed in
          let vt = Pair(sigma_val, r) in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Decode(w1) ->
        if dst = w1.src then
          let a, _ = unPairB m_type in
          let m_term = Ast.mkReturn (Ast.mkFstV (Ast.mkSndV (Ast.mkVar z))) in
          let _, b = unPairB w1.type_forward in
          let project = Typing.check_term [(z, src.message_type)] []
                          (Ast.mkTypeAnnot
                             (Circuit.project b a m_term)
                             (Type.newty (Type.Base b))) in
          let lt, m' = term_to_ssa project in
          let vt = Pair(sigma_val, m') in
          Direct(src, z, lt, vt, label_of_dst w1)
        else assert false
      | Circuit.Tensor(w1, w2, w3) ->
        if dst = w1.src then
          (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
          let _, m'_type = unPairB w3.type_forward in
          let vt = Pair(sigma_val, inl m'_type m_val) in
          Direct(src, z, [], vt, label_of_dst w3)
        else if dst = w2.src then
          (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
          let _, m'_type = unPairB w3.type_forward in
          let vt = Pair(sigma_val, inr m'_type m_val) in
          Direct(src, z, [], vt, label_of_dst w3)
        else if dst = w3.src then
          (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
             <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)
          (* no additional type constraints needed; use variables *)
          let m_type1, m_type2 = unSumB m_type in
          let m' = Ident.fresh "m'" in
          Branch(src, z, [],
                 (Basetype.Data.sumid 2, [m_type1; m_type2], m_val,
                  [(m', Pair(sigma_val, Var(m')), label_of_dst w1);
                   (m', Pair(sigma_val, Var(m')), label_of_dst w2)]))
        else assert false
      | Circuit.Der(w1 (* \Tens A X *), w2 (* X *), (gamma, f)) ->
        if dst = w1.src then
          let m1_type, m2_type = unPairB m_type in
          let m2 = Snd(m_val, m1_type, m2_type) in
          let vt = Pair(sigma_val, m2) in
          Direct(src, z, [], vt, label_of_dst w2)
        else if dst = w2.src then
          let lgamma = bind_context sigma_val sigma_type gamma in
          let lt, c = term_value_to_ssa f in
          let vt = Pair(sigma_val, Pair(c, m_val)) in
          Direct(src, z, lt @ lgamma, vt, label_of_dst w1)
        else assert false
      | Circuit.App(w1 (* (A => X) *), (gamma, f), w2 (* X *)) ->
        if dst = w1.src then
          Direct(src, z, [], Var(z), label_of_dst w2)
        else if dst = w2.src then
          let ltgamma = bind_context sigma_val sigma_type gamma in
          let lt, c = term_value_to_ssa f in
          let vt = Pair(sigma_val, Pair(c, m_val)) in
          Direct(src, z, lt @ ltgamma, vt, label_of_dst w1)
        else assert false
      | Circuit.Door(w1 (* X *), w2 (* \Tens A X *)) ->
        if dst = w1.src then
          let sigma'_type, c_type = unPairB sigma_type in
          let sigma' = Fst(sigma_val, sigma'_type, c_type) in
          let c = Snd(sigma_val, sigma'_type, c_type) in
          let vt = Pair(sigma', Pair(c, m_val)) in
          Direct(src, z, [], vt, label_of_dst w2)
        else if dst = w2.src then
          let c_type, m'_type = unPairB m_type in
          let c = Fst(m_val, c_type, m'_type) in
          let m' = Snd(m_val, c_type, m'_type) in
          let vt = Pair(Pair(sigma_val, c), m') in
          Direct(src, z, [], vt, label_of_dst w1)
        else assert false
      | Circuit.Bind(w1 (* \Tens A X *), w2 (*  A => X *)) ->
        if dst = w1.src then
          let m1_type, b_type = unPairB m_type in
          let b = Snd(m_val, m1_type, b_type) in
          let vt = Pair(sigma_val, b) in
          Direct(src, z, [], vt, label_of_dst w2)
        else if dst = w2.src then
          Direct(src, z, [], Var(z), label_of_dst w1)
        else assert false
      | Circuit.Assoc(w1 (* \Tens (A x B) X *), w2 (* \Tens A \Tens B X *)) ->
        if dst = w1.src then
          let cd_type, m'_type = unPairB m_type in
          let cd = Fst(m_val, cd_type, m'_type) in
          let m' = Snd(m_val, cd_type, m'_type) in
          let c_type, d_type = unPairB cd_type in
          let c = Fst(cd, c_type, d_type) in
          let d = Snd(cd, c_type, d_type) in
          let vt = Pair(sigma_val, Pair(c, Pair(d, m'))) in
          Direct(src, z, [], vt, label_of_dst w2)
        else if dst = w2.src then
          let c_type, dm'_type = unPairB m_type in
          let d_type, m'_type = unPairB dm'_type in
          let c = Fst(m_val, c_type, dm'_type) in
          let dm' = Snd(m_val, c_type, dm'_type) in
          let d = Fst(dm', d_type, m'_type) in
          let m' = Snd(dm', d_type, m'_type) in
          let vt = Pair(sigma_val, Pair(Pair(c, d), m')) in
          Direct(src, z, [], vt, label_of_dst w1)
        else assert false
      | Circuit.Direct(w1 (* (X- => TX+)^* *), w2 (* X *)) ->
        if dst = w1.src then
          Direct(src, z, [], Var(z), label_of_dst w2)
        else if dst = w2.src then
          let vt = Pair(sigma_val, Pair(m_val, Unit)) in
          Direct(src, z, [], vt, label_of_dst w1)
        else assert false
      | Circuit.LWeak(w1 (* \Tens A X *),
                      w2 (* \Tens B X *)) (* B <= A *) ->
        if dst = w1.src then
          let _, a_token = unPairB w1.type_back in
          let a, m'_type = unPairB a_token in
          let _, b_token = unPairB w2.type_forward in
          let b, _ = unPairB b_token in
          let c = Ast.mkReturn (Ast.mkFstV (Ast.mkSndV (Ast.mkVar z))) in
          let project = Typing.check_term [(z, src.message_type)] []
                          (Ast.mkTypeAnnot
                             (Circuit.project b a c)
                             (Type.newty (Type.Base b))) in
          let l = Let((z,  src.message_type), Val(Var(z))) in
          let lt, d = term_to_ssa project in
          let m' = Snd(m_val, a, m'_type) in
          let vt = Pair(sigma_val, Pair(d, m')) in
          Direct(src, z, lt @ [l], vt, label_of_dst w2)
        else if dst = w2.src then
          let _, a_token = unPairB w1.type_forward in
          let a, m'_type = unPairB a_token in
          let _, b_token = unPairB w2.type_back in
          let b, _ = unPairB b_token in
          let c = Ast.mkReturn (Ast.mkFstV (Ast.mkSndV (Ast.mkVar z))) in
          let m' = Snd(m_val, b, m'_type) in
          let embed = Typing.check_term [(z, src.message_type)] []
                        (Ast.mkTypeAnnot
                           (Circuit.embed b a c)
                           (Type.newty (Type.Base a))) in
          let l = Let((z,  src.message_type), Val(Var(z))) in
          let lt, d = term_to_ssa embed in
          let vt = Pair(sigma_val, Pair(d, m')) in
          Direct(src, z, lt @ [l], vt, label_of_dst w1)
        else assert false
      | Circuit.Seq(w1 (* TA^* *), w2 (* \Tensor A TB^* *), w3 (* TB *)) ->
        if dst = w3.src then
          (*   <sigma, m> @ w3      |-->  <sigma, m> @ w1 *)
          Direct(src, z, [], Var z, label_of_dst w1)
        else if dst = w1.src then
          (* <sigma, m> @ w1      |-->  <sigma, m> @ w2 *)
          let vt = Pair(sigma_val, Pair(m_val, Unit)) in
          Direct(src, z, [], vt, label_of_dst w2)
        else if dst = w2.src then
          (* <sigma, m> @ w2  |-->  <sigma, m> @ w3 *)
          let m1_type, m2_type = unPairB m_type in
          let m2 = Snd(m_val, m1_type, m2_type) in
          let vt = Pair(sigma_val, m2) in
          Direct(src, z, [], vt, label_of_dst w3)
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
          let c_type, m'_type = unPairB m_type in
          let c = Fst(m_val, c_type, m'_type) in
          let m' = Snd(m_val, c_type, m'_type) in
          let _, t1m'_type = unPairB w1.type_forward in
          let t1_type, _ = unPairB t1m'_type in
          let t1 = In((id, i, c), t1_type) in
          let vt = Pair(sigma_val, Pair(t1, m')) in
          Direct(src, z, [], vt, label_of_dst w1)
        else if dst = w1.src then
          (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
               <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
          let c_type, m'_type = unPairB m_type in
          let c = Fst(m_val, c_type, m'_type) in
          let m' = Snd(m_val, c_type, m'_type) in
          let y = Ident.fresh "y" in
          Branch(src, z, [],
                 (id, params, c,
                  List.map ws
                    ~f:(fun w ->
                      (y, Pair(sigma_val, Pair(Var(y), m')), label_of_dst w))
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
  let sigma, arg_type = unPairB f.entry_label.message_type in
  Basetype.unify_exn sigma (Basetype.newty Basetype.UnitB);
  List.iter (Basetype.free_vars arg_type)
    ~f:(Basetype.unify_exn (Basetype.newty Basetype.IntB));

  let sigma, ret_type = unPairB f.return_type in

  Basetype.unify_exn sigma (Basetype.newty Basetype.UnitB);
  List.iter (Basetype.free_vars ret_type)
    ~f:(Basetype.unify_exn (Basetype.newty Basetype.IntB));

  let label_names = List.map f.blocks ~f:(fun b -> (label_of_block b).name) in
  let max_label_name = List.fold_right label_names ~f:max ~init:0 in

  let entry_label = {
    name = max_label_name + 1;
    message_type = arg_type} in
  let entry_block =
    let z = Ident.fresh "z" in
    Direct(entry_label, z, [], Pair(Unit, Var z), f.entry_label) in

  let exit_label = {
    name = max_label_name + 2;
    message_type =
      Basetype.newty (
        Basetype.PairB(
          Basetype.newty Basetype.UnitB,
          ret_type))
  } in
  let exit_block =
    let z = Ident.fresh "z" in
    let v = Snd(Var z, Basetype.newty Basetype.UnitB, ret_type) in
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


let of_circuit (name: string) (c: Circuit.t) : t =
  let body = circuit_to_ssa_body name c in
  add_entry_exit_code body
