(** Type inference *)
open Core.Std

(* Contexts *)
type 'a context = (Ident.t * 'a) list

(** Split a context into the part declaring the exactly the
    free variables of a term and the rest.
    The call [take_subcontext gamma t] returns [(gamma1, gamma2)],
    where [gamma1] declares all the free variables of [t] and
    [gamma2] contains the rest of the variables. *)
let take_subcontext (phi: 'a context) (t: Ast.t) =
  let fv = Ast.free_vars t in
  List.partition_tf phi
    ~f:(fun (x, _) -> List.mem fv x)

(** Given a context [gamma] and two terms [t1] and [t2], split the context
    into [(gamma1, gamma2)], such that [gamma1] contains just free variables
    from [t1] and [gamma2] contains just variables from [t2]. If a variable
    appears in both terms, then it may appear in either [gamma1] or [gamma2],
    but not in both. *)
let split_context (phi: 'a context) t1 t2 =
  let phi1, rest = take_subcontext phi t1 in
  let phi2, _ = take_subcontext rest t2 in
  phi1, phi2

exception Typing_error of Ast.t option * string

let eq_expected_constraint t ~expected:expected_ty ~actual:actual_ty =
  try
    Type.unify_exn expected_ty actual_ty
  with
  | Uftype.Cyclic_type ->
    let msg = "Unification leads to cyclic type " ^
              (Printing.string_of_type actual_ty) ^ "." in
    raise (Typing_error(t, msg)) 
  | Uftype.Constructor_mismatch ->
    let msg =
      Printf.sprintf
        "Term has interactive type %s, but a term of type %s is expected."
        (Printing.string_of_type actual_ty)
        (Printing.string_of_type expected_ty) in
    raise (Typing_error(t, msg))
    
let beq_expected_constraint t ~expected:expected_ty ~actual:actual_ty =
  try
    Basetype.unify_exn expected_ty actual_ty
  with
  | Uftype.Cyclic_type ->
    let msg = "Unification leads to cyclic value type " ^
              (Printing.string_of_basetype actual_ty) ^ "." in
    raise (Typing_error(t, msg)) 
  | Uftype.Constructor_mismatch ->
    let msg =
      Printf.sprintf
        "Term has value type %s, but a term of type %s is expected."
        (Printing.string_of_basetype actual_ty)
        (Printing.string_of_basetype expected_ty) in
    raise (Typing_error(t, msg))

(** Value environments *)
module ValEnv:
sig
  type t

  (** Matches the given value against the given pattern and
      adds the resulting variable bindings to the environment. *)
  val match_pattern: t -> Typedterm.value -> Ast.pattern -> t

  (** Find the value of a variable in the environment and update 
      its location as given. *)
  val find: t -> Ident.t -> Ast.Location.t -> Typedterm.value option
  
  val of_context: Basetype.t context -> t
end =
struct  
  type t = (Ast.pattern * Typedterm.value) list

  let rec unify_type p a =
    match p with
    | Ast.PatUnit ->
      beq_expected_constraint None ~actual:a
        ~expected:(Basetype.newty Basetype.UnitB)
    | Ast.PatVar _  -> ()
    | Ast.PatPair(p1, p2) ->
      let alpha = Basetype.newvar() in
      let beta = Basetype.newvar() in
      beq_expected_constraint None
        ~actual:a
        ~expected:(Basetype.newty (Basetype.PairB(alpha, beta)));
      unify_type p1 alpha;
      unify_type p2 beta

  let match_pattern (env: t) (v: Typedterm.value) (p: Ast.pattern) : t =
    unify_type p v.Typedterm.value_type;
    (p, v) :: env

  let find (env: t) (x: Ident.t) (loc: Ast.Location.t)
    : Typedterm.value option =
    let rec find_pattern (p: Ast.pattern) (v: Typedterm.value) =
      match p with
      | Ast.PatUnit -> None
      | Ast.PatVar(y) ->
        if x = y then Some v else None
      | Ast.PatPair(p1, p2) ->
        let a1, a2 =
          match Basetype.case v.Typedterm.value_type with
          | Basetype.Sgn(Basetype.PairB(a1, a2)) -> a1, a2
          | _ -> assert false in
        let v1 = { Typedterm.value_desc = Typedterm.FstV v;
                   Typedterm.value_type = a1;
                   Typedterm.value_loc = loc } in
        match find_pattern p1 v1 with
        | Some w -> Some w
        | None ->
          let v2 = { Typedterm.value_desc = Typedterm.SndV v;
                     Typedterm.value_type = a2;
                     Typedterm.value_loc = loc } in
          find_pattern p2 v2 in
    let rec find (env: t) =
      match env with
      | [] -> None
      | (p, v) :: rest ->
        match find_pattern p v with
        | None -> find rest
        | Some x -> Some x in
    find env
      
  let of_context (c: Basetype.t context) : t =
    List.map c
      ~f:(fun (x, a) ->
        let v = { Typedterm.value_desc = Typedterm.VarV x;
                  Typedterm.value_type = a;
                  Typedterm.value_loc = Ast.Location.none } in
        (Ast.PatVar(x), v))
end

let rec ptV (c: ValEnv.t) (t: Ast.t)
  : Typedterm.value =
  let open Typedterm in
  match t.Ast.desc with
  | Ast.Var(v: Ident.t) ->
    begin
      match ValEnv.find c v (t.Ast.loc) with
      | Some a -> a
      | None ->
        let msg = "Variable '" ^ (Ident.to_string v) ^
                  "' not bound or not of value type." in
        raise (Typing_error (Some t, msg))
    end
  | Ast.ConstV(Ast.Cintconst(_) as c) ->
     { value_desc = ConstV(c);
       value_type = Basetype.newty Basetype.IntB;
       value_loc = t.Ast.loc }
  | Ast.ConstV(Ast.Cundef(a) as c) ->
    { value_desc = ConstV(c);
      value_type = a;
      value_loc = t.Ast.loc }
  | Ast.UnitV ->
    { value_desc = UnitV;
      value_type = Basetype.newty Basetype.UnitB;
      value_loc = t.Ast.loc }
  | Ast.PairV(t1, t2) ->
      let b1 = ptV c t1 in
      let b2 = ptV c t2 in
      { value_desc = PairV(b1, b2);
        value_type = Basetype.newty (Basetype.PairB(b1.value_type, b2.value_type));
        value_loc = t.Ast.loc }
  | Ast.FstV(t1) ->
    let a1 = ptV c t1 in
    let a = Basetype.newvar() in
    let b = Basetype.newvar() in
    let expected = Basetype.newty (Basetype.PairB(a, b)) in
    beq_expected_constraint (Some t1)
      ~actual:a1.value_type
      ~expected:expected;
    { value_desc = FstV(a1);
      value_type = a;
      value_loc = t.Ast.loc }
  | Ast.SndV(t1) ->
    let a1 = ptV c t1 in
    let a = Basetype.newvar() in
    let b = Basetype.newvar() in
    let expected = Basetype.newty (Basetype.PairB(a, b)) in
    beq_expected_constraint (Some t1)
      ~actual:a1.value_type
      ~expected:expected;
    { value_desc = SndV(a1);
      value_type = b;
      value_loc = t.Ast.loc }
  | Ast.InV(id, k, t1) ->
    let a1 = ptV c t1 in
    let n = Basetype.Data.param_count id in
    let params = List.init n ~f:(fun _ -> Basetype.newvar ()) in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    let argtype =
      match List.nth (Basetype.Data.constructor_types id params) k with
      | Some a -> a
      | None ->
        let msg = "No such constructor" in
        raise (Typing_error (Some t, msg)) in
    beq_expected_constraint (Some t1) ~actual:a1.value_type ~expected:argtype;
    { value_desc = InV(id, k, a1);
      value_type = data;
      value_loc = t.Ast.loc }
  | Ast.SelectV(id, params, s, i) ->
    assert (not (Basetype.Data.is_discriminated id));
    let a1 = ptV c s in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    let ctypes = Basetype.Data.constructor_types id params in
    let ai = List.nth_exn ctypes i in
    beq_expected_constraint (Some s) ~actual:a1.value_type ~expected:data;
    { value_desc = SelectV(id, params, a1, i);
      value_type = ai;
      value_loc = t.Ast.loc }
  | Ast.Return _ | Ast.Bind _ | Ast.Fn _ | Ast.Fun _ | Ast.App _ |Ast.Case _
  | Ast.Copy _ | Ast.Direct _ | Ast.TypeAnnot _ | Ast.Const _
  | Ast.Pair _ | Ast.LetPair _
    -> raise (Typing_error (Some t, "Value term expected."))
and pt (c: ValEnv.t) (phi: Type.t context) (t: Ast.t)
  : Typedterm.t =
  let open Typedterm in
  match t.Ast.desc with
  | Ast.Var(v: Ident.t) ->
    let a =
      match List.Assoc.find phi v with
      | Some a -> a
      | None ->
        let msg = "Variable '" ^ (Ident.to_string v) ^ "' not bound." ^
                  "Is it a value variable or has it been used elsewhere?" in
        raise (Typing_error (Some t, msg)) in
    { t_desc = Typedterm.Var(v);
      t_type = a;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cprint _ as c) ->
    let a = Type.newty
              (Type.FunV(
                 Basetype.newty Basetype.UnitB,
                 Type.newty (Type.Base (Basetype.newty Basetype.UnitB)))) in
    { t_desc = Const(c);
      t_type = a;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cintprint as c) ->
    let a = Type.newty
              (Type.FunV(
                 Basetype.newty Basetype.IntB,
                 Type.newty (Type.Base (Basetype.newty Basetype.UnitB)))) in
    { t_desc = Const(c);
      t_type = a;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cintadd as c)
  | Ast.Const(Ast.Cintsub as c)
  | Ast.Const(Ast.Cintmul as c)
  | Ast.Const(Ast.Cintdiv as c)
  | Ast.Const(Ast.Cintshl as c)
  | Ast.Const(Ast.Cintshr as c)
  | Ast.Const(Ast.Cintsar as c)
  | Ast.Const(Ast.Cintand as c)
  | Ast.Const(Ast.Cintor as c)
  | Ast.Const(Ast.Cintxor as c) ->
    let intty = Basetype.newty Basetype.IntB in
    let a = Type.newty (Type.FunV(Basetype.newty (Basetype.PairB(intty, intty)),
                                  Type.newty (Type.Base intty))) in
    { t_desc = Const(c);
      t_type = a;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cinteq as c)
  | Ast.Const(Ast.Cintlt as c)
  | Ast.Const(Ast.Cintslt as c) ->
    let intty = Basetype.newty Basetype.IntB in
    let boolty = Basetype.newty (Basetype.DataB(Basetype.Data.boolid, [])) in
    let a = Type.newty (Type.FunV(Basetype.newty (Basetype.PairB(intty, intty)),
                                  Type.newty (Type.Base boolty))) in
    { t_desc = Const(c);
      t_type = a;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cpush(a) as c) ->
    let b = Type.newty
              (Type.FunV
                 (a, Type.newty (Type.Base (Basetype.newty Basetype.UnitB)))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cpop(a) as c) ->
    let b = Type.newty (Type.FunV(Basetype.newty Basetype.UnitB,
                                  Type.newty (Type.Base a))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Calloc(a) as c) ->
    let boxa = Basetype.newty (Basetype.BoxB a) in
    let b = Type.newty (Type.FunV(Basetype.newty Basetype.UnitB,
                                  Type.newty (Type.Base boxa))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cfree(a) as c) ->
    let unitB = Basetype.newty (Basetype.UnitB) in
    let b = Type.newty (Type.FunV(Basetype.newty (Basetype.BoxB a),
                                  Type.newty (Type.Base unitB))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cload(a) as c) ->
    let b = Type.newty (Type.FunV(Basetype.newty (Basetype.BoxB a),
                                  Type.newty (Type.Base a))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Cstore(a) as c) ->
    let boxa = Basetype.newty (Basetype.BoxB a) in
    let unitB = Basetype.newty (Basetype.UnitB) in
    let b = Type.newty (Type.FunV(Basetype.newty (Basetype.PairB(boxa, a)),
                                  Type.newty (Type.Base unitB))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Carrayalloc(a) as c) ->
    let arraya = Basetype.newty (Basetype.ArrayB a) in
    let b = Type.newty (Type.FunV(Basetype.newty Basetype.IntB,
                                  Type.newty (Type.Base arraya))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Carrayfree(a) as c) ->
    let unitB = Basetype.newty (Basetype.UnitB) in
    let b = Type.newty (Type.FunV(Basetype.newty (Basetype.ArrayB a),
                                  Type.newty (Type.Base unitB))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Carrayget(a) as c) ->
    let arraya = Basetype.newty (Basetype.ArrayB a) in
    let boxa = Basetype.newty (Basetype.BoxB a) in
    let intB = Basetype.newty Basetype.IntB in
    let b = Type.newty (Type.FunV(Basetype.newty (Basetype.PairB(arraya, intB)),
                                  Type.newty (Type.Base boxa))) in
    { t_desc = Const(c);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc}
  | Ast.Const(Ast.Ccall(_, a, b) as c) ->
    let d = Type.newty (Type.FunV(a, Type.newty (Type.Base b))) in
    { t_desc = Const(c);
      t_type = d;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Const(Ast.Cencode(a) as c) ->
    let b = Basetype.newty (Basetype.EncodedB(Basetype.newvar())) in
    let d = Type.newty (Type.FunV(a, Type.newty (Type.Base b))) in
    { t_desc = Const(c);
      t_type = d;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Const(Ast.Cdecode(b) as c) ->
    let a = Basetype.newty (Basetype.EncodedB(Basetype.newvar())) in
    let d = Type.newty (Type.FunV(a, Type.newty (Type.Base b))) in
    { t_desc = Const(c);
      t_type = d;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Return(t1) ->
    let a1 = ptV c t1 in
    { t_desc = Return(a1);
      t_type = Type.newty (Type.Base a1.value_type);
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Bind(t1, (p, t2)) ->
    let phi1, phi2 = split_context phi t1 t2 in
    let a1 = pt c phi1 t1 in
    let pat_id = Ident.fresh "pat" in
    let pat_val = { value_desc = VarV(pat_id);
                    value_type = Basetype.newvar();
                    value_loc = Ast.Location.none } in
    let cpat = ValEnv.match_pattern c pat_val p in
    let a2 = pt cpat phi2 t2 in
    let beta = Basetype.newvar() in
    eq_expected_constraint (Some t1) ~actual:a1.t_type
      ~expected:(Type.newty (Type.Base pat_val.value_type));
    eq_expected_constraint (Some t2) ~actual:a2.t_type
      ~expected:(Type.newty (Type.Base beta));
    { t_desc = Bind((a1, pat_val.value_type), (pat_id, a2));
      t_type = a2.t_type;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Fn(p, t1) ->
    let pat_id = Ident.fresh "pat" in
    let pat_val = { value_desc = VarV(pat_id);
                    value_type = Basetype.newvar();
                    value_loc = Ast.Location.none } in
    let c1 = ValEnv.match_pattern c pat_val p in
    let b1 = pt c1 phi t1 in
    { t_desc = Fn((pat_id, pat_val.value_type), b1);
      t_type = Type.newty (Type.FunV(pat_val.value_type, b1.t_type));
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.App(s, t) ->
    let t_is_int_var =
      match t.Ast.desc with
      | Ast.Var v -> List.Assoc.mem phi v
      | _ -> false in
    begin
      if Ast.is_value t && (not t_is_int_var) then
        begin
        let beta = Type.newvar() in
        let a1 = ptV c t in
        let b = pt c phi s in
        eq_expected_constraint (Some s)
          ~actual:b.t_type
          ~expected:(Type.newty (Type.FunV(a1.value_type, beta)));
        { t_desc = AppV(b, a1);
          t_type = beta;
          t_context = phi;
          t_loc = t.Ast.loc }
        end
      else
        begin
        let gamma, delta = split_context phi s t in
        let s1 = pt c gamma s in
        let alpha = Basetype.newvar() in
        let betaY = Type.newvar() in
        let t1 = pt c delta t in
        eq_expected_constraint (Some s)
          ~actual:s1.t_type
          ~expected:(Type.newty (Type.FunI(alpha, t1.t_type, betaY)));
        { t_desc = AppI(s1, t1);
          t_type = betaY;
          t_context = phi;
          t_loc = t.Ast.loc }
        end
    end
  | Ast.Fun((x, alpha, ty), t) ->
    let t1 = pt c ((x, ty) :: phi) t in
    { t_desc = Fun((x, alpha, ty), t1);
      t_type = Type.newty (Type.FunI(alpha, ty, t1.t_type));
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Copy(s, (xs, t)) ->
    let gamma, delta = split_context phi s t in
    let beta = Type.newvar() in
    let delta1 = List.map ~f:(fun x -> (x, beta)) xs in
    let t1 = pt c (delta1 @ delta) t in
    let s1 = pt c gamma s in
    eq_expected_constraint (Some s) ~actual:s1.t_type ~expected:beta;
    { t_desc = Copy(s1, (xs, t1));
      t_type = t1.t_type;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Pair(s, t) ->
    let gamma, delta = split_context phi s t in
    let s1 = pt c gamma s in
    let t1 = pt c delta t in
    { t_desc = Pair(s1, t1);
      t_type = Type.newty (Type.Tensor(s1.t_type, t1.t_type));
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.LetPair(s, (x, y, t)) ->
    let alpha = Type.newvar() in
    let beta = Type.newvar() in
    let gamma, rest = take_subcontext phi s in
    let delta, _ = take_subcontext rest t in
    let s1 = pt c gamma s in
    let t1 = pt c ([(x, alpha); (y, beta)] @ delta) t in
    let ab = Type.newty (Type.Tensor(alpha, beta)) in
    eq_expected_constraint (Some s) ~actual:s1.t_type ~expected:ab;
    { t_desc = LetPair(s1, ((x, alpha), (y, beta), t1));
      t_type = t1.t_type;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Case(id, s, l) ->
    assert (Basetype.Data.is_discriminated id);
    (* case distinction is allowed over values only *)
    let s1 = ptV c s in
    let n = Basetype.Data.param_count id in
    let params = List.init n ~f:(fun _ -> Basetype.newvar ()) in
    let data = Basetype.newty (Basetype.DataB(id, params)) in
    let argtypes = Basetype.Data.constructor_types id params in
    let beta = Type.newvar() in
    let l_args = List.zip_exn l argtypes in
    let l1 = List.map l_args
               ~f:(fun ((p, u), argty) ->
                 let pat_id = Ident.fresh "pat" in
                 let pat_val = { value_desc = VarV(pat_id);
                                 value_type = argty;
                                 value_loc = Ast.Location.none } in
                 let cz = ValEnv.match_pattern c pat_val p in
                 let a2 = pt cz phi u in
                 eq_expected_constraint (Some u) ~actual:a2.t_type ~expected:beta;
                 pat_id, a2) in
    beq_expected_constraint (Some s) ~actual:s1.value_type ~expected:data;
    { t_desc = Case(id, params, s1, l1);
      t_type = beta;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.Direct(b, s) ->
    let s1 = pt c [] s in
    let b' = Type.map_index_types b
               (fun a ->
                  begin
                    match Basetype.case a with
                    | Basetype.Var -> ()
                    | _ -> print_string
                             ("Warning: Non-variable index type annotations " ^
                              "are ignored.\n")
                  end;
                  Basetype.newvar()) in
    let b_minus, b_plus =
      Type.question_answer_pair b' in
    eq_expected_constraint (Some t)
      ~actual:s1.t_type
      ~expected:(Type.newty (Type.FunV(b_minus,
                                       Type.newty (Type.Base b_plus))));
    { t_desc = Direct(b, s1);
      t_type = b;
      t_context = phi;
      t_loc = t.Ast.loc }
  | Ast.TypeAnnot(t, ty) ->
    (* TODO: move to type/basetype *)
    let rec check_wf_base (b: Basetype.t) : unit =
      match Basetype.case b with
      | Basetype.Var -> ()
      | Basetype.Sgn sb ->
        begin
          match sb with
          | Basetype.IntB | Basetype.ZeroB | Basetype.UnitB -> ()
          | Basetype.EncodedB(b1)
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
                let n = Basetype.Data.param_count id in
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
        end in
    let rec check_wf (b: Type.t) : unit =
      match Type.case b with
      | Type.Var -> ()
      | Type.Sgn sb ->
        begin
        match sb with
        | Type.Base(b) ->
          check_wf_base b
        | Type.Tensor(b1, b2) ->
          check_wf b1; check_wf b2
        | Type.FunV(b1, b2) ->
          check_wf_base b1; check_wf b2
        | Type.FunI(a1, b1, b2) ->
          check_wf_base a1; check_wf b1; check_wf b2
        end in
    check_wf ty;
    let t1 = pt c phi t in
    eq_expected_constraint (Some t) ~actual:t1.t_type ~expected:ty;
    t1
  | Ast.ConstV _ | Ast.UnitV | Ast.PairV _ | Ast.InV _
  | Ast.FstV _ | Ast.SndV _ | Ast.SelectV _
    ->
    raise (Typing_error (Some t, "Interactive term expected."))

let check_value (c: Basetype.t context) (t: Ast.t) : Typedterm.value =
  ptV (ValEnv.of_context c) t

let check_term (c: Basetype.t context) (phi: Type.t context) (t: Ast.t)
  : Typedterm.t =
  pt (ValEnv.of_context c) phi t
