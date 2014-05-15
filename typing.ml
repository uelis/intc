(** Type inference
*)
open Core.Std
open Term
open Unify

(* Contexts *)
type 'a context = (var * 'a) list

let take_subcontext (phi: 'a context) (t: Term.t) =
  let fv = Term.free_vars t in
  List.partition_tf phi
    ~f:(fun (x, _) -> List.mem fv x)

let split_context (phi: 'a context) t1 t2 =
  let phi1, rest = take_subcontext phi t1 in
  let phi2, _ = take_subcontext rest t2 in
  phi1, phi2

(* Unification *)
type eq_tag = Term.t * (unit -> string)
module U = Unify(struct type t = eq_tag end)

let eq_expected_constraint t ~expected:expected_ty ~actual:actual_ty = 
  let msg () = 
    Printf.sprintf "Term has type %s, but a term of type %s is expected."
      (Printing.string_of_type actual_ty)
      (Printing.string_of_type expected_ty) in
  U.unify_eqs [U.Type_eq(expected_ty, actual_ty, Some(t, msg))]
let beq_expected_constraint t ~expected:expected_ty ~actual:actual_ty = 
  let msg () = 
    Printf.sprintf "Term has type %s, but a term of type %s is expected."
      (Printing.string_of_basetype actual_ty) 
      (Printing.string_of_basetype expected_ty) in
  U.unify_eqs [U.Basetype_eq(expected_ty, actual_ty, Some(t, msg))]

exception Typing_error of Term.t option * string                            

let raise_error (failed_eqn: U.failure_reason) =
  let raise_cyclic sactual tag =
    match tag with
    | Some (term, msg) -> 
      raise (Typing_error(Some(term), msg()))
    | None ->
      let msg = "Unification leads to cyclic type " ^ sactual^ "." in
      raise (Typing_error(None, msg)) in
  let raise_eqn_failed sactual sexpected tag =
    match tag with
    | Some (term, msg) ->
      raise (Typing_error (Some term, msg()))
    | None -> 
      let msg = Printf.sprintf "Cannot unify %s and %s." sactual sexpected in
      raise (Typing_error(None, msg)) in         
  match failed_eqn with
    | U.Cyclic_type(U.Type_eq(actual, _, tag)) ->
      let sactual = Printing.string_of_type actual in
      raise_cyclic sactual tag
    | U.Cyclic_type(U.Basetype_eq(actual, _, tag)) ->
      let sactual = Printing.string_of_basetype actual in
      raise_cyclic sactual tag
    | U.Equation_failed(U.Type_eq(actual, expected, tag)) ->
      let sactual = Printing.string_of_type actual in
      let sexpected = Printing.string_of_type expected in
      raise_eqn_failed sactual sexpected tag
    | U.Equation_failed(U.Basetype_eq(actual, expected, tag)) ->
      let sactual = Printing.string_of_basetype actual in
      let sexpected = Printing.string_of_basetype expected in
      raise_eqn_failed sactual sexpected tag


let rec fresh_tyVars n = 
  if n = 0 then [] 
  else (Basetype.newty Basetype.Var) :: (fresh_tyVars (n-1))    

let rec ptW (c: Basetype.t context) (phi: Type.t context) (t: Term.t) 
  : Basetype.t =
  match t.Term.desc with
  | Term.Var(v: var) ->
    begin 
      match List.Assoc.find c v with
      | Some a -> a
      | None ->
        raise (Typing_error (Some t, "Variable '" ^ v ^ 
                                     "' not bound or not of value type."))
    end
  | ValW(Cintconst(_)) ->
    Basetype.newty Basetype.NatW 
  | ValW(Cundef(a)) ->
    a
  | UnitW ->
    Basetype.newty Basetype.OneW
  | Box(t1, a1) ->
    let phi1, _ = take_subcontext phi t1 in
    let b1 = ptW c phi1 t1 in
    beq_expected_constraint t1 ~actual:b1 ~expected:a1;
    Basetype.newty (Basetype.BoxW(a1))
  | Unbox(t1, a1) ->
    let phi1, _ = take_subcontext phi t1 in
    let b1 = ptW c phi1 t1 in
    let alpha = Basetype.newtyvar () in
    let boxalpha = Basetype.newty (Basetype.BoxW(alpha)) in
    beq_expected_constraint t ~actual:b1 ~expected:boxalpha;
    beq_expected_constraint t1 ~actual:alpha ~expected:a1;
    alpha
  | PairW((t1, a1), (t2, a2)) ->
      let phi1, phi2 = split_context phi t1 t2 in
      let b1 = ptW c phi1 t1 in
      let b2 = ptW c phi2 t2 in
      beq_expected_constraint t1 ~actual:b1 ~expected:a1;
      beq_expected_constraint t2 ~actual:b2 ~expected:a2;
      Basetype.newty (Basetype.TensorW(b1, b2))
  | FstW(t1, a, b) ->
    let phi1, _ = take_subcontext phi t1 in
    let a1 = ptW c phi1 t1 in
    beq_expected_constraint t1 ~actual:a1 ~expected:(Basetype.newty (Basetype.TensorW(a, b)));
    a
  | SndW(t1, a, b) ->
    let phi1, _ = take_subcontext phi t1 in
    let a1 = ptW c phi1 t1 in
    beq_expected_constraint t1 ~actual:a1 ~expected:(Basetype.newty (Basetype.TensorW(a, b)));
    b
  | InW((id, k, t1), a) ->
    let phi1, _ = take_subcontext phi t1 in
    let a1 = ptW c phi1 t1 in
    let n = Basetype.Data.params id in
    let params = fresh_tyVars n in
    let data = Basetype.newty (Basetype.DataW(id, params)) in
    (* TODO: check that constructor exists? *)
    let argtype = List.nth_exn (Basetype.Data.constructor_types id params) k in
    let fresh_data, fresh_argtype = data, argtype in
    (*
      match Basetype.freshen_list [data; argtype] with
      | [fd; fa] -> fd, fa 
      | _ -> assert false in*)
    beq_expected_constraint t1 ~actual:a1 ~expected:fresh_argtype;
    beq_expected_constraint t ~actual:fresh_data ~expected:a;
    fresh_data
  | Select(id, params, s, i) -> 
    assert (not (Basetype.Data.is_discriminated id));
    let phis, _ = take_subcontext phi s in
    let a1 = ptW c phis s in
    let data = Basetype.newty (Basetype.DataW(id, params)) in
    let ctypes = Basetype.Data.constructor_types id params in
    let ai = List.nth_exn ctypes i in
    beq_expected_constraint s ~actual:a1 ~expected:data;
    ai
  | Case(id, params, s, l) ->
    (* TODO: verify lenghts *)
    assert (Basetype.Data.is_discriminated id);
    let phis, phirest = take_subcontext phi s in
    let a1 = ptW c phis s in
    let data = Basetype.newty (Basetype.DataW(id, params)) in
    let argtypes = Basetype.Data.constructor_types id params in
    let beta = Basetype.newty Basetype.Var in
    let l_args = List.zip_exn l argtypes in 
    ignore (List.fold_right l_args
              ~f:(fun ((x, u), argty) phirest -> 
                let phiu, newrest = take_subcontext phirest u in
                let a2 = ptW ((x, argty) :: c) phiu u in
                beq_expected_constraint u ~actual:a2 ~expected:beta;
                newrest)
              ~init:phirest);
    beq_expected_constraint s ~actual:a1 ~expected:data;
    beta 
  | App(s, a, t) ->
    let phi1, phi2 = split_context phi s t in
    let beta = Basetype.newty Basetype.Var in
    let a1 = ptU c phi1 s in
    let a2 = ptW c phi2 t in
    eq_expected_constraint s ~actual:a1 ~expected:(Type.newty (Type.FunW(a2, beta)));
    eq_expected_constraint s ~actual:a1 ~expected:a;
    beta 
  | BindW((t1, a), (xc, t2)) ->
    let phi1, phi2 = split_context phi t1 t2 in
    let a1 = ptW c phi1 t1 in
    let a2 = ptW ((xc, a)::c) phi2 t2 in
    beq_expected_constraint t1 ~actual:a1 ~expected:a; 
    a2
  | LambdaW _ | LambdaU _ | CopyU _ | HackU _ | TypeAnnot _ 
  | ConstW _  | ExternalU _
    -> raise (Typing_error (Some t, "Interactive term not expected here."))
and ptU (c: Basetype.t context) (phi: Type.t context) (t: Term.t) 
  : Type.t =
  match t.Term.desc with
  | Term.Var(v: var) ->
    begin 
      match List.Assoc.find phi v with
      | Some a -> a
      | None -> 
        raise (Typing_error (Some t, "Variable '" ^ v ^ 
                                     "' not bound. Has it been used elsewhere?"))
    end
  | ConstW(Cprint _) ->
    Type.newty (Type.FunW(Basetype.newty Basetype.OneW, 
                          Basetype.newty Basetype.OneW)) 
  | ConstW(Cintprint) ->
    Type.newty (Type.FunW(Basetype.newty Basetype.NatW, 
                          Basetype.newty Basetype.OneW)) 
  | ConstW(Cintadd) 
  | ConstW(Cintsub) 
  | ConstW(Cintmul) 
  | ConstW(Cintdiv) ->
    let intty = Basetype.newty Basetype.NatW in        
    Type.newty (Type.FunW(Basetype.newty (Basetype.TensorW(intty, intty)), 
                        intty)) 
  | ConstW(Cinteq) ->
    let intty = Basetype.newty Basetype.NatW in        
    let boolty = Basetype.newty (Basetype.DataW(Basetype.Data.boolid, [])) in
    Type.newty (Type.FunW(Basetype.newty (Basetype.TensorW(intty, intty)), 
                boolty)) 
  | ConstW(Cintslt) ->
    let intty = Basetype.newty Basetype.NatW in        
    let boolty = Basetype.newty (Basetype.DataW(Basetype.Data.boolid, [])) in
    Type.newty (Type.FunW(Basetype.newty (Basetype.TensorW(intty, intty)), 
                boolty)) 
  | ConstW(Cpush(a)) ->
    Type.newty (Type.FunW(a, Basetype.newty Basetype.OneW)) 
  | ConstW(Cpop(a)) ->
    Type.newty (Type.FunW(Basetype.newty Basetype.OneW, a)) 
  | ConstW(Ccall(_, a, b)) ->
    Type.newty (Type.FunW(a, b)) 
  | LambdaW((x, a), t1) ->
    let alpha = Basetype.newty Basetype.Var in
    let a1 = ptW ((x, alpha) :: c) phi t1 in
    beq_expected_constraint (Term.mkVar x) ~actual:alpha ~expected:a; 
    Type.newty (Type.FunW(alpha, a1)) 
  | App(s, a, t) ->
    let gamma, delta = split_context phi s t in
    let tyFun = ptU c gamma s in
    let alpha = Basetype.newty Basetype.Var in
    let betaY = Type.newty Type.Var in
    let tyX = ptU c delta t in
    eq_expected_constraint s 
      ~actual:tyFun 
      ~expected:(Type.newty (Type.FunU(alpha, tyX, betaY)));
    eq_expected_constraint s ~actual:tyFun ~expected:a;
    betaY
  | LambdaU((x, a, ty), t) ->
    let beta = Type.newty Type.Var in
    let tyY = ptU c ((x, beta) :: phi) t in
    eq_expected_constraint (Term.mkVar x) ~actual:beta ~expected:ty;
    Type.newty (Type.FunU(a, beta, tyY))
  | CopyU(s, (x, y, t)) ->
    let gamma, delta = split_context phi s t in
    let beta = Type.newty Type.Var in
    let tyY = ptU c ([(x, beta); (y, beta)] @ delta) t in
    let tyX = ptU c gamma s in
    eq_expected_constraint s ~actual:tyX ~expected:beta;
    tyY
  | Case(id, params, s, l) -> 
    assert (Basetype.Data.is_discriminated id);
    if not (Term.is_pure s) then
      raise (Typing_error (Some s, "Only pure terms are allowed here."));
    (* TODO: can allow open terms here!?! *)
    let a1 = ptW c [] s in
    let data = Basetype.newty (Basetype.DataW(id, params)) in
    let argtypes = Basetype.Data.constructor_types id params in
    let beta = Type.newty Type.Var in
    let l_args = List.zip_exn l argtypes in 
    List.iter l_args
      ~f:(fun ((x, u), argty) -> 
        let a2 = ptU ((x, argty) :: c) phi u in
        eq_expected_constraint u ~actual:a2 ~expected:beta);
    beq_expected_constraint s ~actual:a1 ~expected:data;
    beta
  | HackU(b, t1) ->
    let a1 = ptU c [] t1 in
    let b_minus, b_plus = 
      Type.question_answer_pair (Type.freshen_index_types b) in
    eq_expected_constraint t 
      ~actual:a1 
      ~expected:(Type.newty (Type.FunW(b_minus, b_plus)));
    b
  | ExternalU((_, a), b) ->
    eq_expected_constraint t 
      ~actual:b 
      ~expected:(Type.freshen a);
    b
  | TypeAnnot(t, ty) ->
    (* TODO: move to type/basetype *)
    let rec check_wf_base (b: Basetype.t) : unit =
      match (Basetype.find b).Basetype.desc with
      | Basetype.Var | Basetype.NatW | Basetype.ZeroW | Basetype.OneW -> ()
      | Basetype.BoxW(b1) -> 
        check_wf_base b1 
      | Basetype.TensorW(b1, b2) -> 
        check_wf_base b1; 
        check_wf_base b2
      | Basetype.DataW(id, bs) -> 
        begin
          try 
            let n = Basetype.Data.params id in
            if List.length bs <> n then 
              let error_msg =
                Printf.sprintf "Data type %s takes %i argument(s)." id n in
              raise (Typing_error(Some t, error_msg))
            else 
              List.iter bs ~f:check_wf_base
          with Not_found -> 
              let error_msg =
                Printf.sprintf "The data type %s is undefined." id in
              raise (Typing_error(Some t, error_msg))
        end
      | Basetype.Link _ -> assert false in
    let rec check_wf (b: Type.t) : unit =
      match Type.finddesc b with
      | Type.Var -> ()
      | Type.FunW(b1, b2) -> 
        check_wf_base b1; check_wf_base b2
      | Type.FunU(a1, b1, b2) -> 
        check_wf_base a1; check_wf b1; check_wf b2
      | Type.Link _ -> assert false in
    check_wf ty;
    let a = ptU c phi t in
    eq_expected_constraint t ~actual:a ~expected:ty;
    a
  | ValW _ | UnitW | PairW _ | InW _ | FstW _ | SndW _ | BindW _ | Box _ | Unbox _  
  | Select _
    -> raise (Typing_error (Some t, "Value term not expected here."))

let principal_typeW (c: Basetype.t context) (phi: Type.t context) (t: Term.t) : Basetype.t =
  try
    ptW c phi t 
  with 
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt

let principal_type (c: Basetype.t context) (phi: Type.t context) (t: Term.t) : Type.t = 
  try
    ptU c phi t
  with 
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt

(*
let rec reconstructW (c: contextW) (phi: contextU) (t: Term.t) 
  : Basetype.t =
  match t.Term.desc with
  | Term.Var(v: var) -> List.assoc v c
  | ConstW(Cintconst(_)) -> Basetype.newty Basetype.NatW
  | ConstW(Cundef(a)) -> a
  | UnitW -> Basetype.newty Basetype.OneW
  | Box(t1, a1) -> Basetype.newty (Basetype.BoxW(a1))
  | Unbox(t1, a1) -> a1
  | PairW((t1, a1), (t2, a2)) ->
    Basetype.newty (Basetype.TensorW(a1, a2))
  | LetW(t1, ((x, a), (y, b), t2)) ->
      let phi1, phi2 = split_context phi t1 t2 in
      let phi2' = undot phi2 in
      reconstructW ([(y, b); (x, a)] @ c) phi2' t2 
  | InW((id, k, t1), a) -> a
  | Case(id, (s, a), []) -> 
    Basetype.newtyvar ()
  | Case(id, (s, a), (x, t)::cases) -> 
    begin
      match Basetype.finddesc a with
      | Basetype.DataW(id, params) ->
        let argtypes = Basetype.Data.constructor_types id params in
        assert (argtypes <> []);
        let xa = List.hd argtypes in
        reconstructW ((x, xa)::c) phi t
      | _ ->
        assert false
    end
  | App(s, a, t) ->
    begin
      match Type.finddesc a with
      | Type.FunW(_, b) -> b
      | _ ->
        assert false
    end
  | BindW((t1, a), (xc, t2)) ->
    let phi1, banged_phi2 = split_context phi t1 t2 in
    let phi2 = undot banged_phi2 in
    reconstructW ((xc, a)::c) phi2 t2 
  | LambdaW _ | LambdaU _ | CopyU _ | HackU _ | TypeAnnot _ 
  | ConstW _
  -> raise (Typing_error (Some t, " Interactive term not expected here."))
and reconstructU (c: contextW) (phi: contextU) (t: Term.t) 
  : Type.t =
  match t.Term.desc with
  | Term.Var(v: var) ->
      let (tyW, tyX) = List.assoc v phi in 
      tyX
  | ConstW(Cprint s) ->
    newty (FunW(Basetype.newty Basetype.OneW, 
                        Basetype.newty Basetype.OneW)) 
  | ConstW(Cintprint) ->
    newty (FunW(Basetype.newty Basetype.NatW, 
                        Basetype.newty Basetype.OneW)) 
  | ConstW(Cintadd) 
  | ConstW(Cintsub) 
  | ConstW(Cintmul) 
  | ConstW(Cintdiv) ->
    let intty = Basetype.newty Basetype.NatW in        
    newty (FunW(Basetype.newty (Basetype.TensorW(intty, intty)), 
                        intty)) 
  | ConstW(Cinteq) | ConstW(Cintslt) ->
    let intty = Basetype.newty Basetype.NatW in        
    let boolty = Basetype.newty (Basetype.DataW(Basetype.Data.boolid, [])) in
    newty (FunW(Basetype.newty (Basetype.TensorW(intty, intty)), 
                        boolty)) 
  | ConstW(Cpush(a)) ->
    newty (FunW(a, Basetype.newty Basetype.OneW)) 
  | ConstW(Cpop(a)) ->
    newty (FunW(Basetype.newty Basetype.OneW, a))
  | LambdaW((x, a), t1) ->
    let a1 = reconstructW ((x, a) :: c) phi t1 in
    newty (FunW(a, a1)) 
  | App(s, a, t) ->
    begin
      match Type.finddesc a with
      | Type.FunU(_, _, b) -> b
      | _ ->
        assert false
    end
  | LambdaU((x, a), t) ->
    let tyY, conY = reconstructU c ((x, (alpha, beta)) :: phi) t in
    newty (FunU(alpha, beta, tyY)),
    eq_expected_constraint (Term.mkVar x) (beta, a) :: conY
  | CopyU(s, (x, y, t)) ->
    let banged_gamma, delta = split_context phi s t in
    let alpha1 = Basetype.newty Basetype.Var in
    let alpha2 = Basetype.newty Basetype.Var in
    let beta = newty Var in
    let tyY, conY = reconstructU c ([(x, (alpha1, beta)); 
                            (y, (alpha2, beta))] @ 
                           delta) 
                      t in
    let gamma = fresh_index_types banged_gamma in
    let sumalpha12 = 
      Basetype.newty 
        (Basetype.DataW(Basetype.Data.sumid 2, [alpha1; alpha2])) in
    let conC = leq_index_types (dot sumalpha12 gamma) banged_gamma in
    let tyX, conX = reconstructU c gamma s in
    tyY,
    eq_expected_constraint s (tyX, beta) ::
    conX @ conC @ conY
  | Case(id, (s, a), l) -> 
    (* TODO: s must be value !*)
    let a1, con1 = reconstructW c [] s in
    (* TODO: appears twice *)
    let fresh_data, fresh_argtypes =
      let n = Basetype.Data.params id in
      let params = fresh_tyVars n in
      let data = Basetype.newty (Basetype.DataW(id, params)) in
      let argtypes = Basetype.Data.constructor_types id params in
      match Basetype.freshen_list (data :: argtypes) with
      | fd :: fas -> fd, fas 
      | _ -> assert false in
    let beta = newty Var in
    let l_args = List.combine l fresh_argtypes in 
    let cons = List.fold_right 
                 (fun ((x, u), argty) cons -> 
                    let a2, con2 = reconstructU ((x, argty) :: c) phi u in
                    eq_expected_constraint u (a2, beta) :: con2 @ cons) 
                 l_args con1 in
    beta, 
    beq_expected_constraint s (a, fresh_data) :: 
    beq_expected_constraint s (a1, fresh_data) :: cons
  | HackU(b, t1) ->
    let a1, con1 = reconstructU c [] t1 in
    let b_minus, b_plus = 
      Type.question_answer_pair (Type.freshen_index_types b) in
    (* TODO
       (fun beta -> 
       raise (Typing_error ("Type annotations on hack must not " ^
       " contain type variables!")))
    *)
    (b, 
     eq_expected_constraint t (newty (FunW(b_minus, b_plus)), a1) ::
     con1)
  | TypeAnnot(t, ty) ->
    (* TODO: move to type/basetype *)
    let rec check_wf_base (b: Basetype.t) : unit =
      match (Basetype.find b).Basetype.desc with
      | Basetype.Var | Basetype.NatW | Basetype.ZeroW | Basetype.OneW -> ()
      | Basetype.BoxW(b1) -> 
        check_wf_base b1 
      | Basetype.TensorW(b1, b2) -> 
        check_wf_base b1; 
        check_wf_base b2
      | Basetype.DataW(id, bs) -> 
        begin
          try 
            let n = Basetype.Data.params id in
            if List.length bs <> n then 
              let error_msg =
                Printf.sprintf "Data type %s takes %i argument(s)." id n in
              raise (Typing_error(Some t, error_msg))
            else 
              List.iter check_wf_base bs
          with Not_found -> 
              let error_msg =
                Printf.sprintf "The data type %s is undefined." id in
              raise (Typing_error(Some t, error_msg))
        end
      | Basetype.Link _ -> assert false in
    let rec check_wf (b: t) : unit =
      match (find b).desc with
      | Var -> ()
      | FunW(b1, b2) -> 
        check_wf_base b1; check_wf_base b2
      | FunU(a1, b1, b2) -> 
        check_wf_base a1; check_wf b1; check_wf b2
      | Link _ -> assert false in
    check_wf ty;
    let a, con = reconstructU c phi t in
    a,
    eq_expected_constraint t (a, ty) :: con
  | UnitW | PairW _ | LetW _ | InW _ | BindW _ | Box _ | Unbox _  
  | ConstW (Cundef _ | Cintconst _)
  -> raise (Typing_error (Some t, " Value term not expected here."))

*)
