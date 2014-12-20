(** Type inference *)
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

let rec ptV (c: Basetype.t context) (t: Term.t)
  : Basetype.t =
  match t.Term.desc with
  | Term.Var(v: var) ->
    begin
      match List.Assoc.find c v with
      | Some a -> a
      | None ->
        raise (Typing_error
                 (Some t, "Variable '" ^ v ^
                          "' not bound or not of value type."))
    end
  | ConstV(Cintconst(_)) ->
    Basetype.newty Basetype.IntB
  | ConstV(Cundef(a)) ->
    a
  | UnitV ->
    Basetype.newty Basetype.UnitB
  | PairV((t1, a1), (t2, a2)) ->
      let b1 = ptV c t1 in
      let b2 = ptV c t2 in
      beq_expected_constraint t1 ~actual:b1 ~expected:a1;
      beq_expected_constraint t2 ~actual:b2 ~expected:a2;
      Basetype.newty (Basetype.PairB(b1, b2))
  | FstV(t1, a, b) ->
    let a1 = ptV c t1 in
    beq_expected_constraint t1
      ~actual:a1
      ~expected:(Basetype.newty (Basetype.PairB(a, b)));
    a
  | SndV(t1, a, b) ->
    let a1 = ptV c t1 in
    beq_expected_constraint t1
      ~actual:a1
      ~expected:(Basetype.newty (Basetype.PairB(a, b)));
    b
  | InV((id, k, t1), a) ->
    let a1 = ptV c t1 in
    let n = Basetype.Data.params id in
    let params = fresh_tyVars n in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    (* TODO: check that constructor exists? *)
    let argtype =
      match List.nth (Basetype.Data.constructor_types id params) k with
      | Some a -> a
      | None ->
        let msg = "No such constructor" in
        raise (Typing_error (Some t, msg)) in
    let fresh_data, fresh_argtype = data, argtype in
    (*
      match Basetype.freshen_list [data; argtype] with
      | [fd; fa] -> fd, fa
      | _ -> assert false in*)
    beq_expected_constraint t1 ~actual:a1 ~expected:fresh_argtype;
    beq_expected_constraint t ~actual:fresh_data ~expected:a;
    fresh_data
  | SelectV(id, params, s, i) ->
    assert (not (Basetype.Data.is_discriminated id));
    let a1 = ptV c s in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    let ctypes = Basetype.Data.constructor_types id params in
    let ai = List.nth_exn ctypes i in
    beq_expected_constraint s ~actual:a1 ~expected:data;
    ai
  | Return _ | Bind _ | Fn _ | Fun _ | App _ |Case _
  | Copy _ | Direct _ | TypeAnnot _ | Const _  | External _
  | Pair _ | LetPair _
    -> raise (Typing_error (Some t, "Value term expected."))
and pt (c: Basetype.t context) (phi: Type.t context) (t: Term.t)
  : Type.t =
  match t.Term.desc with
  | Term.Var(v: var) ->
    begin
      match List.Assoc.find phi v with
      | Some a -> a
      | None ->
        let msg = "Variable '" ^ v ^ "' not bound. " ^
                  "Is it a value variable or has it been used elsewhere?" in
        raise (Typing_error (Some t, msg))
    end
  | Const(Cprint _) ->
    Type.newty
      (Type.FunV(
         Basetype.newty Basetype.UnitB,
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Cintprint) ->
    Type.newty
      (Type.FunV(
         Basetype.newty Basetype.IntB,
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Cintadd)
  | Const(Cintsub)
  | Const(Cintmul)
  | Const(Cintdiv)
  | Const(Cintshl)
  | Const(Cintshr)
  | Const(Cintsar)
  | Const(Cintand)
  | Const(Cintor)
  | Const(Cintxor) ->
    let intty = Basetype.newty Basetype.IntB in
    Type.newty (
      Type.FunV(
        Basetype.newty (Basetype.PairB(intty, intty)),
        Type.newty (Type.Base intty)))
  | Const(Cinteq) 
  | Const(Cintslt) ->
    let intty = Basetype.newty Basetype.IntB in
    let boolty = Basetype.newty (Basetype.DataB(Basetype.Data.boolid, [])) in
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.PairB(intty, intty)),
         Type.newty (Type.Base boolty)))
  | Const(Cpush(a)) ->
    Type.newty
      (Type.FunV(
         a,
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Cpop(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty Basetype.UnitB,
         Type.newty (Type.Base a)))
  | Const(Calloc(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty Basetype.UnitB,
         Type.newty (Type.Base (Basetype.newty (Basetype.BoxB a)))))
  | Const(Cfree(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.BoxB a),
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Cload(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.BoxB a),
         Type.newty (Type.Base a)))
  | Const(Cstore(a)) ->
    let boxa = Basetype.newty (Basetype.BoxB a) in
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.PairB(boxa, a)),
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Carrayalloc(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty Basetype.IntB,
         Type.newty (Type.Base (Basetype.newty (Basetype.ArrayB a)))))
  | Const(Carrayfree(a)) ->
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.ArrayB a),
         Type.newty (Type.Base (Basetype.newty Basetype.UnitB))))
  | Const(Carrayget(a)) ->
    let arraya = Basetype.newty (Basetype.ArrayB a) in
    let boxa = Basetype.newty (Basetype.BoxB a) in
    let intB = Basetype.newty Basetype.IntB in
    Type.newty
      (Type.FunV(
         Basetype.newty (Basetype.PairB(arraya, intB)),
         Type.newty (Type.Base boxa)))
  | Const(Ccall(_, a, b)) | Const(Cencode(a, b)) | Const(Cdecode(a, b)) ->
    Type.newty (Type.FunV(a, Type.newty (Type.Base b)))
  | Return(t1, a) ->
    let a1 = ptV c t1 in
    beq_expected_constraint t1 ~actual:a1 ~expected:a;
    Type.newty (Type.Base a1)
  | Bind((t1, a), (xc, t2)) ->
    let phi1, phi2 = split_context phi t1 t2 in
    let a1 = pt c phi1 t1 in
    let a2 = pt ((xc, a)::c) phi2 t2 in
    let beta = Basetype.newty Basetype.Var in
    eq_expected_constraint t1 ~actual:a1
      ~expected:(Type.newty (Type.Base a));
    eq_expected_constraint t2 ~actual:a2
      ~expected:(Type.newty (Type.Base beta));
    a2
  | Fn((x, a), t1) ->
    let alpha = Basetype.newty Basetype.Var in
    let b1 = pt ((x, alpha) :: c) phi t1 in
    beq_expected_constraint (Term.mkVar x) ~actual:alpha ~expected:a;
    Type.newty (Type.FunV(alpha, b1))
  | App(s, a, t) ->
    let t_is_int_var =
      match t.desc with
      | Var v -> List.Assoc.mem phi v
      | _ -> false in
    begin
      if Term.is_value t && (not t_is_int_var) then
        begin
        let beta = Type.newty Type.Var in
        let a1 = ptV c t in
        let b = pt c phi s in
        eq_expected_constraint s
          ~actual:b
          ~expected:(Type.newty (Type.FunV(a1, beta)));
        eq_expected_constraint s ~actual:b ~expected:a;
        beta
        end
      else
        begin
        let gamma, delta = split_context phi s t in
        let tyFun = pt c gamma s in
        let alpha = Basetype.newty Basetype.Var in
        let betaY = Type.newty Type.Var in
        let tyX = pt c delta t in
        eq_expected_constraint s
          ~actual:tyFun
          ~expected:(Type.newty (Type.FunI(alpha, tyX, betaY)));
        eq_expected_constraint s ~actual:tyFun ~expected:a;
        betaY
        end
    end
  | Fun((x, a, ty), t) ->
    let beta = Type.newty Type.Var in
    let tyY = pt c ((x, beta) :: phi) t in
    eq_expected_constraint (Term.mkVar x) ~actual:beta ~expected:ty;
    Type.newty (Type.FunI(a, beta, tyY))
  | Copy(s, (x, y, t)) ->
    let gamma, delta = split_context phi s t in
    let beta = Type.newty Type.Var in
    let tyY = pt c ([(x, beta); (y, beta)] @ delta) t in
    let tyX = pt c gamma s in
    eq_expected_constraint s ~actual:tyX ~expected:beta;
    tyY
  | Pair(s, t) ->
    let gamma, delta = split_context phi s t in
    let tyX = pt c gamma s in
    let tyY = pt c delta t in
    Type.newty (Type.Tensor(tyX, tyY))
  | LetPair(s, ((x, a), (y, b), t)) ->
    if x = y then
      raise (Typing_error (Some t, "Duplicate variable in pattern."));
    let gamma, rest = take_subcontext phi s in
    let delta, _ = take_subcontext rest t in
    let tyX = pt c gamma s in
    let tyY = pt c ([(x, a); (y, b)] @ delta) t in
    let ab = Type.newty (Type.Tensor(a, b)) in
    eq_expected_constraint s ~actual:tyX ~expected:ab;
    tyY
  | Case(id, params, s, l) ->
    assert (Basetype.Data.is_discriminated id);
    (* case distinction is allowed over values only *)
    let a1 = ptV c s in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    let argtypes = Basetype.Data.constructor_types id params in
    let beta = Type.newty Type.Var in
    let l_args = List.zip_exn l argtypes in
    List.iter l_args
      ~f:(fun ((x, u), argty) ->
        let a2 = pt ((x, argty) :: c) phi u in
        eq_expected_constraint u ~actual:a2 ~expected:beta);
    beq_expected_constraint s ~actual:a1 ~expected:data;
    beta
  | Direct(b, t1) ->
    let a1 = pt c [] t1 in
    let b' = Type.map_index_types b
               (fun a ->
                  begin
                    match Basetype.finddesc a with
                    | Basetype.Var -> ()
                    | _ -> print_string
                             ("Warning: Non-variable index type annotations " ^
                              "are ignored.\n")
                  end;
                  Basetype.newtyvar()) in
    let b_minus, b_plus =
      Type.question_answer_pair b' in
    eq_expected_constraint t
      ~actual:a1
      ~expected:(Type.newty
                   (Type.FunV(
                      b_minus,
                      Type.newty (Type.Base b_plus))));
    b
  | External((_, a), b) ->
    eq_expected_constraint t
      ~actual:b
      ~expected:(Type.freshen a);
    b
  | TypeAnnot(t, ty) ->
    (* TODO: move to type/basetype *)
    let rec check_wf_base (b: Basetype.t) : unit =
      match (Basetype.find b).Basetype.desc with
      | Basetype.Var | Basetype.IntB | Basetype.ZeroB | Basetype.UnitB -> ()
      | Basetype.BoxB(b1) ->
        check_wf_base b1
      | Basetype.ArrayB(b1) ->
        check_wf_base b1
      | Basetype.PairB(b1, b2) ->
        check_wf_base b1;
        check_wf_base b2
      | Basetype.DataB(id, bs) ->
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
      | Type.Base(b) ->
        check_wf_base b
      | Type.Tensor(b1, b2) ->
        check_wf b1; check_wf b2
      | Type.FunV(b1, b2) ->
        check_wf_base b1; check_wf b2
      | Type.FunI(a1, b1, b2) ->
        check_wf_base a1; check_wf b1; check_wf b2
      | Type.Link _ -> assert false in
    check_wf ty;
    let a = pt c phi t in
    eq_expected_constraint t ~actual:a ~expected:ty;
    a
  | ConstV _ | UnitV | PairV _ | InV _ | FstV _ | SndV _ | SelectV _
    ->
    raise (Typing_error (Some t, "Interactive term expected."))

let principal_type_value (c: Basetype.t context) (t: Term.t) : Basetype.t =
  try
    ptV c t
  with
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt

let principal_type (c: Basetype.t context) (phi: Type.t context) (t: Term.t) : Type.t =
  try
    pt c phi t
  with
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt
