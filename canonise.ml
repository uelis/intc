open Core.Std
open Term
open Unify

(*
Case can contain a pure term.
*)

module U = Unify(struct type t = unit end)

(* TODO: explain *)
let external_glue (f: string) (a: Basetype.t) (b: Basetype.t): Term.t =
  let fresh_var = Vargen.mkVarGenerator "m" ~avoid:[] in
  (* Für jede Typvariable alpha eine Termvariable für jedes Vorkommen
     wählen*)
  (* unmarshaling *)
  let um a rel x =
    let rec um a x =
      match Basetype.finddesc a with
      | NatW | OneW | ZeroW -> 
        mkVar x
      | Var -> 
        Printf.printf "%i\n" (Basetype.find a).id;
        begin
          match Int.Map.find rel (Basetype.find a).id with
          | None -> mkTerm (ValW(Cundef(Basetype.newtyvar())))
          | Some xs ->
            List.mapi xs ~f:(fun i x -> i, x)
            |> List.fold_right 
                 ~f:(fun (i, y) t ->
                   let e = fresh_var () in
                   mkBindW (mkApp 
                              (mkConstW(Cinteq)) 
                              (mkPairW (mkTerm (ValW(Cintconst i))) (mkVar x)))
                     (e, mkCase Basetype.Data.boolid (mkVar e)
                           [ unusable_var, mkVar y;
                             unusable_var, t]))
                 ~init:(mkTerm (ValW(Cundef(Basetype.newtyvar()))))
        end
      | TensorW(a1, a2) ->
        let x1 = fresh_var () in
        let x2 = fresh_var () in
        let v1 = um a1 x1 in
        let v2 = um a2 x2 in
        Term.subst (mkFstW (mkVar x)) x1 
          (Term.subst (mkSndW (mkVar x)) x2 (Term.mkPairW v1 v2))
      | DataW(id, params) -> 
        let cases = 
          Basetype.Data.constructor_types id params
          |> List.mapi ~f:(fun i ai ->
            let y = fresh_var () in
            (y, mkInW id i (um ai y))) in
        mkCase id (mkVar x) cases
      | BoxW(_) -> 
        failwith "todo"
      | Link _ -> assert false in
    um a x in
  (* marshaling *)
  let rec m (g: Basetype.t Typing.context) (v, rel) =
    match g with
    | [] -> 
      (* TODO: this doesn't work with boxed types ! *)
      let nat = Basetype.newty (Basetype.NatW) in
      let a' = Basetype.subst (fun _ -> nat) a in
      let b' = Basetype.subst (fun _ -> nat) b in
      let z = fresh_var () in
      let t = mkApp (mkConstW (Ccall(f, a', b'))) v in
      Printing.print_term t;
      mkBindW t (z, um b rel z)
    (* make call with v, rel and decode *)
    | (x, a) :: gs ->
      match Basetype.finddesc a with
      | NatW | OneW | ZeroW ->
        m gs (v, rel)
      | Var -> 
        (* nothing to match. add x to relation, substitute in value *)
        let aid = (Basetype.find a).id in
        let xs = Int.Map.find rel aid
                 |> Option.value ~default:[] in 
        let i = List.length xs in
        let v' = subst (mkTerm (ValW(Cintconst(i)))) x v in
        let rel' = Int.Map.add rel ~key:aid ~data:(xs @ [x]) in
        Printf.printf "%i\n" aid;
        m gs (v', rel')
      | TensorW(a1, a2) ->
        let x1 = fresh_var () in
        let x2 = fresh_var () in
        let v' = subst (mkPairW (mkVar x1) (mkVar x2)) x v in
        Term.subst (mkFstW (mkVar x)) x1 
          (Term.subst (mkSndW (mkVar x)) x2 
             (m ((x1, a1) :: (x2, a2) :: gs) (v', rel)))
      | DataW(id, params) -> 
        let cases = 
          Basetype.Data.constructor_types id params
          |> List.mapi ~f:(fun i ai ->
            let y = fresh_var () in
            (y, 
             let v' = subst (mkInW id i (mkVar y)) x v in
             m ((y, ai) :: gs) (v', rel))) in
        mkCase id (mkVar x) cases
      | BoxW(_) -> 
        failwith "todo"
      | Link _ -> assert false in
  let x = fresh_var () in
  let a' = Basetype.newtyvar () in
  let t = mkLambdaW ((x, a'), m [(x, a)] (mkVar x, Int.Map.empty)) in
  let ty = Typing.principal_type [] [] t in
  Printf.printf "%s\n"
    (Printing.string_of_type ty);
  t

type let_binding =
  | Let of (Term.var * Basetype.t) * Term.t

let rec mkLets lt v =
  match lt, v.desc with 
  | [], _ -> v
  | Let((x, _), t) :: lt', _ when Term.is_value t -> 
    mkLets lt' (Term.subst t x v)
  | Let((x, a), t) :: lt', Var z ->
    if x = z then mkLets lt' t else 
      mkLets lt' (mkTerm (BindW((t, a), (x, v))))
  | Let((x, a), t) :: lt', _ ->
    mkLets lt' (mkTerm (BindW((t, a), (x, v))))

(* TODO: specify and simplify ! *)
let canonise(term: Term.t) =
  let fresh_var =
    let vars = all_vars term in
    Vargen.mkVarGenerator "x" ~avoid:vars in
  let rec canoniseW(term: Term.t) =
    match term.desc with
    | Var _ 
    | ValW _
    | ConstW _
    | UnitW -> [], term
    | InW((n, k, s), a) -> 
      let ls, vs = canoniseW s in
      ls, { term with desc = InW((n, k, vs), a) }
    | FstW(s, a, b) -> 
      let ls, vs = canoniseW s in
      ls, { term with desc = FstW(vs, a, b) }
    | SndW(s, a, b) -> 
      let ls, vs = canoniseW s in
      ls, { term with desc = SndW(vs, a, b) }
    | Box(s, a) -> 
      let ls, vs = canoniseW s in
      let x = fresh_var () in
      let boxa = Basetype.newty (Basetype.BoxW a) in
      Let((x, boxa), { term with desc = Box(vs, a) }) :: ls,
      mkVar x
    | Unbox(s, a) -> 
      let ls, vs = canoniseW s in
      let x = fresh_var () in
      Let((x, a), { term with desc = Unbox(vs, a) }) :: ls,
      mkVar x
    | PairW((s, a), (t, b)) -> 
      let ls, vs = canoniseW s in
      let lt, vt = canoniseW t in
      lt @ ls, { term with desc = PairW((vs, a), (vt, b)) }
    | App(s, a, t) -> 
      let vs = canoniseU s in
      let lt, vt = canoniseW t in
      let x = fresh_var () in
      let b = match Type.finddesc a with
        | Type.FunW(_, a2) -> a2
        | _ -> assert false in
      Let((x, b), { term with desc = App(vs, a, vt) }) :: lt,
      mkVar x
    | BindW((s, a), (x, t)) -> 
      let ls, vs = canoniseW s in
      let lt, vt = canoniseW t in
      lt @ [Let((x, a), vs)] @ ls, vt
    | Select(id, params, s, i) ->
      assert (not (Basetype.Data.is_discriminated id));
      let ls, vs = canoniseW s in
      let s' = Select(id, params, vs, i) in
      let a = List.nth_exn (Basetype.Data.constructor_types id params) i in
      let x = fresh_var () in
      Let((x, a), mkTerm s') :: ls, 
      { term with desc = Var(x) }               
    | Case(id, params, s, l) ->
      assert (Basetype.Data.is_discriminated id);
      let ls, vs = canoniseW s in
      let s' = Case(id, params, vs,
                    List.map l ~f:(fun (x, t) -> 
                      let lt, vt = canoniseW t in
                      (x, mkLets lt vt))) in
      let x = fresh_var () in
      Let((x, Basetype.newtyvar() (* TODO! *)), mkTerm s') :: ls, 
      { term with desc = Var(x) }               
    | LambdaW (_, _)
    | LambdaU (_, _)
    | CopyU (_, _) 
    | HackU (_, _)
    | ExternalU (_, _)
    | TypeAnnot (_, _) ->
      assert false
  and canoniseU(term : Term.t) =
    match term.Term.desc with
    | Var _ 
    | ValW _
    | ConstW _
      -> term
    | CopyU(s, (x, y, t)) -> 
      { term with 
        desc = CopyU(canoniseU s, (x, y, canoniseU t)) } 
    | LambdaW((x, ty), t) -> 
      let lt, vt = canoniseW t in
      { term with 
        desc = LambdaW((x, ty), mkLets lt vt) } 
    | LambdaU((x, a, ty), t) -> 
      { term with 
        desc = LambdaU((x, a, ty), canoniseU t) } 
    | App(s, a, t) -> 
      { term with desc = App(canoniseU s, a, canoniseU t) }
    | Case(id, params, s, l) ->
      assert (Term.is_pure s);
      { term with 
        desc = Case(id, params, s, 
                    List.map l ~f:(fun (x, t) -> (x, canoniseU t))) } 
    | HackU(ty, s) -> 
      { term with 
        desc = HackU(ty, canoniseU s) }
    | TypeAnnot(t, ty) -> 
      { term with 
        desc = TypeAnnot(canoniseU t, ty) } 
    | ExternalU((e, a), b) ->
      let am, ap = Type.question_answer_pair a in      
      let eg = external_glue e am ap in
      let t = { term with
        desc = HackU(b, canoniseU eg) } in
                Printing.print_term t;
        t
    | UnitW 
    | PairW _
    | InW _
    | FstW _
    | SndW _
    | Select _ 
    | BindW _
    | Box _
    | Unbox _ ->
      Printing.print_term term;
      assert false in
  let canonised_term = canoniseU term in
  (* currently needed to fill in type annotations *)
  ignore (Typing.principal_type [] [] canonised_term);
  canonised_term
