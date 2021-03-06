(** Compilation to circuits
  * TODO:
  *  - simplify boilerplate
  *  - construct circuit with the correct types right away,
  *    without using type inference
*)
open Core.Std
open Typing

(** A wire represents a dart in an undirected graph. *)
type wire = {
  src: Ident.t;
  dst: Ident.t;
  type_forward: Basetype.t;
  type_back: Basetype.t
}

let flip (w: wire) = {
  src = w.dst;
  dst = w.src;
  type_forward = w.type_back;
  type_back = w.type_forward
}

type value_context = Basetype.t Typing.context

(* All wires are meant to 'leave' the instructions, i.e. they are all affixed
*  with their src-label to the instruction.
*  The type of the respective wires is indicated in the comments. *)
type instruction =
  | Base of wire (* TA *) * (Basetype.t Typing.context * Typedterm.t)
  | Seq of wire (* (TA)^* *) * wire (* \Tens A (TB)^* *) * wire (* TB *)
  | Encode of wire (* A => B *)
  | Decode of wire (* B => A *)
  | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
  | Der of wire (* \Tens A X *) * wire (* X *) * (Basetype.t Typing.context * Typedterm.value)
  | Case of Basetype.Data.id * Basetype.t list * wire * (wire list)
  | Door of wire (* X *) * wire (* \Tens A X *)
  | Assoc of wire (* \Tens (A x B) X *) * wire (* \Tens A (\Tens B X) *)
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B \lhd A *)
  | Bind of wire (* \Tens A X *) * wire (* (A -> X) *)
  | App of wire (* (A -> X) *) * (Basetype.t Typing.context * Typedterm.value) * wire (* X *)
  | Direct of wire (* (X- -> X+) *) * wire (* X *)

type t = {
  output : wire;
  instructions : instruction list
}

let wires (i: instruction) : wire list =
  match i with
  | Base(w, _) | Encode(w) | Decode(w) -> [w]
  | Der(w1, w2, _) | Door(w1, w2) | Assoc(w1, w2) | LWeak(w1, w2)
  | Bind(w1, w2) | App(w1, _, w2) | Direct(w1, w2) -> [w1; w2]
  | Seq(w1, w2, w3) | Tensor(w1, w2, w3) -> [w1; w2; w3]
  | Case(_, _, w1, ws) -> w1 :: ws

let tensor s t = Basetype.newty (Basetype.PairB(s, t))
let sum s t = Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [s; t]))

(**
  * Compilation of an interactive term to a circuit.
  *
  * The diagram is assumed to reside in a box of the functor
  * {\Tens {An * ... * A1}}. The components of the tuples
  * are named by the variable names in sigma.
  *
  * Arguments:
  * - sigma: Names with which the components can be accessed.
  *     sigma = [c1; ... ;cn] means that c1 corresponds to
  *     A1 and cn to An
  * - gamma: Names of the wires for the context variables.
  *     They are directed so as to go into the diagram.
  * - t: the term that is to be compiled.
  *
  * Result:
  * - The wire that comes out of the diagram with the value of
  *   the term t.
  * - The circuit as a list of instructions.
  *)
(* ASSUMPTION: all type annotations in t may only contain index types
 * that are variables, i.e. not {1+1}'a --o 'b, for example. *)
let raw_circuit_of_term  (sigma: value_context) (gamma: wire context)
      (t: Typedterm.t): t =
  let restrict_context gamma t =
    List.filter gamma
      ~f:(fun (x, _) -> List.Assoc.mem t.Typedterm.t_context x) in
  let remove_context gamma ls =
    List.filter gamma ~f:(fun (x, _) -> not (List.mem ls x)) in
  let fresh_wire () =
    { src = Ident.fresh "wire";
      dst = Ident.fresh "wire";
      type_forward = Basetype.newvar();
      type_back = Basetype.newvar()
    } in
  let rec enter_box (gamma: wire context) : (wire context) * instruction list =
    match gamma with
    | [] -> ([], [])
    | (x, w) :: rest ->
      let (d, i) = enter_box rest in
      let w1 = fresh_wire () in
      let w2 = fresh_wire () in
      let w3 = fresh_wire () in
      (x, w3) :: d,
      LWeak(flip w, w1) :: Assoc(flip w1, w2) :: Door(w3, flip w2) :: i
  in
  let rec compile (sigma: value_context) (gamma: wire context)
            (t: Typedterm.t) =
    match t.Typedterm.t_desc with
    | Typedterm.Var(x) ->
      let wx = List.Assoc.find_exn gamma x in
      let w = fresh_wire () in
      let w' = fresh_wire () in
      let v = { Typedterm.value_desc = Typedterm.UnitV;
                Typedterm.value_type = Basetype.newty Basetype.UnitB;
                Typedterm.value_loc = Ast.Location.none } in
      w, [Der(flip w', w, (sigma, v)); LWeak(flip wx, w')]
    | Typedterm.Return(_) ->
      let w = fresh_wire () in
      w, [Base(w, (sigma, t))]
    | Typedterm.Direct(ty, t) ->
      let tym, typ = Type.question_answer_pair ty in
      let w_t, i_t = compile sigma gamma t in
      let w = fresh_wire () in
      let sigma = Basetype.newvar() in
      Basetype.unify_exn w.type_back (tensor sigma tym);
      Basetype.unify_exn w.type_forward (tensor sigma typ);
      w, Direct(flip w_t, w) :: i_t
    | Typedterm.AppV(s, v) ->
      let wr = fresh_wire () in
      let w_s, i_s = compile sigma gamma s in
      wr, App(flip w_s, (sigma, v), wr) :: i_s
    | Typedterm.AppI(s, t) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = restrict_context gamma t in
      let w_s, i_s = compile sigma gamma_s s in
      let alpha = Basetype.newvar() in
      let w_t, i_t =
        compile_in_box (Ident.fresh "unused", alpha) sigma gamma_t t in
      let wr = fresh_wire () in
      (wr, Tensor(flip w_t, wr, flip w_s) :: i_s @ i_t)
    | Typedterm.Pair(s, t) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = restrict_context gamma t in
      let w_s, i_s = compile sigma gamma_s s in
      let w_t, i_t = compile sigma gamma_t t in
      let wr = fresh_wire () in
      wr, Tensor(flip w_s, flip w_t, wr) :: i_s @ i_t
    | Typedterm.LetPair(s, ((x, _), (y, _), t)) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = remove_context (restrict_context gamma t) [x; y] in
      let gamma_s_inbox, i_enter_box = enter_box gamma_s in
      let alpha = Basetype.newvar() in
      let sigma_s = ((Ident.fresh "unused", alpha) ::sigma) in
      let w_s, i_s = compile sigma_s gamma_s_inbox s in
      let w_s_left = fresh_wire () in
      let w_s_right = fresh_wire () in
      let i_unpair = [Tensor(w_s_left, w_s_right, flip w_s)] in
      let w_x = fresh_wire () in
      let w_y = fresh_wire () in
      let i_leavebox = [Door(flip w_s_left, w_x);
                        Door(flip w_s_right, w_y)] in
      let (w_t, i_t) = compile sigma ((y, w_y) :: (x, w_x) :: gamma_t) t in
      w_t, i_t @ i_s @ i_enter_box @ i_unpair @ i_leavebox
    | Typedterm.Copy(s, (xs, t)) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = remove_context (restrict_context gamma t) xs in
      let alpha = Basetype.newvar() in
      let w_s, i_s =
        compile_in_box (Ident.fresh "unused", alpha) sigma gamma_s s in
      let delta  = List.map ~f:(fun x -> (x, fresh_wire())) xs in
      let ws = List.map ~f:(fun (_, w) -> w) delta in
      let w_types = List.map ~f:(fun _ -> Basetype.newvar()) ws in
      let n = List.length ws in
      let w_t, i_t = compile sigma (delta @ gamma_t) t in
      (* TODO: check that types are really inferred! *)
      (w_t, Case(Basetype.Data.sumid n, w_types,
                 flip w_s, ws) :: i_s @ i_t)
    | Typedterm.Case(id, params, f, ts) ->
      let n = List.length ts in
      let case_types = Basetype.Data.constructor_types id params in
      let ts_typed = List.map2_exn ts case_types
                       ~f:(fun (x, t) a -> ((x, a), t)) in
      let copy_and_enter_wire (w: wire)
        : wire list * instruction list =
        let w'= fresh_wire () in
        let ws = List.init n ~f:(fun _ -> fresh_wire ()) in
        let ws_in_box = List.init n ~f:(fun _ -> fresh_wire ()) in
        let doors = List.map (List.zip_exn ws ws_in_box)
                      ~f:(fun (w, w_in_box) -> Door(w_in_box, flip w)) in
        ws_in_box,
        [Der(w', flip w, (sigma, f));
         Case(id, params, flip w', ws)] @ doors
      in
      let rec copy_and_enter_ctx (c: wire context)
        : (wire context) list * instruction list =
        match c with
        | [] -> (List.init n ~f:(fun _ -> []), [])
        | (x, w) :: rest ->
          let (ws, is) = copy_and_enter_wire w in
          let (cs, i') = copy_and_enter_ctx rest in
          (List.map ~f:(fun (w, c) -> (x, w) :: c) (List.zip_exn ws cs),
           is @ i')
      in
      let (gammas, i_dup) = copy_and_enter_ctx gamma in
      let (ts_in_box, i_ts) =
        (List.fold_right (List.zip_exn gammas ts_typed)
           ~f:(fun (gamma, ((x, a), t)) (ws, is) ->
           let w', is' = compile ((x, a) :: sigma) gamma t in
           w' :: ws, is' @ is)
           ~init:([], [])) in
      let ws = List.init n ~f:(fun _ -> fresh_wire ()) in
      let i_leavebox = List.map (List.zip_exn ts_in_box ws)
                         ~f:(fun (t, w) -> Door(flip t, w)) in
      let w_join = fresh_wire () in
      let i_join = [Case(id, params, w_join, List.map ~f:flip ws)] in
      let sigmaty = Basetype.newvar() in
      let qty = Basetype.newvar() in
      let data = Basetype.newty (Basetype.DataB(id, params)) in
      Basetype.unify_exn w_join.type_back (tensor sigmaty (tensor data qty));
      let w = fresh_wire () in
      let i_der = [Der(flip w_join, w, (sigma, f))] in
      (w, i_der @ i_join @ i_leavebox @ i_ts @ i_dup)
    | Typedterm.Fun((x, a, ty), s) ->
      let tym, typ = Type.question_answer_pair ty in
      let sigma1 = Basetype.newvar() in
      let sigma2 = Basetype.newvar() in
      (* ASSUMPTION: all annotations must have type variables as index
       * types.
       * TODO: Give a warning otherwise! *)
      let wx =
        { (fresh_wire ()) with
          type_forward = tensor sigma1 (tensor a typ);
          type_back = tensor sigma2 (tensor a tym)} in
      let w = fresh_wire () in
      let w_s, i_s = (compile sigma ((x, wx) :: gamma) s) in
      w, Tensor(wx, flip w_s, w) :: i_s
    | Typedterm.Fn((x, a), t) ->
      let w_t, i_t = compile_in_box (x, a) sigma gamma t in
      let sigmat = Basetype.newvar() in
      let beta = Basetype.newvar() in
      Basetype.unify_exn w_t.type_back (tensor sigmat (tensor a beta));
      let w = fresh_wire () in
      w, Bind(flip w_t, w) :: i_t
    | Typedterm.Bind((s, a), (c, t)) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = restrict_context gamma t in
      let wr = fresh_wire () in
      let w_s, i_s = compile sigma gamma_s s in
      let w_t, i_t = compile_in_box (c, a) sigma gamma_t t in
      let sigma = Basetype.newvar() in
      Basetype.unify_exn w_s.type_forward (tensor sigma a); (* TODO *)
      wr, Seq(flip w_s, flip w_t, wr) ::
          i_s @ i_t
    | Typedterm.Const(Ast.Cencode(a)) ->
      let w = fresh_wire () in
      let sigma = Basetype.newvar() in
      let unitB = Basetype.newty Basetype.UnitB in
      Basetype.unify_exn w.type_back (tensor sigma (tensor a unitB));
      w, [Encode(w)]
    | Typedterm.Const(Ast.Cdecode(b)) ->
      let w = fresh_wire () in
      let sigma = Basetype.newvar() in
      Basetype.unify_exn w.type_forward (tensor sigma b);
      w, [Decode(w)]
    | Typedterm.Const(_) ->
      let w = fresh_wire () in
      let w1 = fresh_wire () in
      let w2 = fresh_wire () in
      let xv = Ident.fresh "x" in
      let x, a, b =
        match Type.case t.Typedterm.t_type with
        | Type.Sgn (Type.FunV(a, b)) ->
          { Typedterm.value_desc = Typedterm.VarV xv;
            Typedterm.value_type = a;
            Typedterm.value_loc = Ast.Location.none },
          a, b
        | _ -> assert false in
      let v =
        { Typedterm.t_desc = Typedterm.AppV(t, x);
          Typedterm.t_type = b;
          Typedterm.t_context = t.Typedterm.t_context;
          Typedterm.t_loc = Ast.Location.none } in
      w, [Bind(flip w1, w); Door(flip w2, w1);
          Base(w2, ((xv, a) :: sigma, v))]
  and compile_in_box ((c: Ident.t), (a: Basetype.t))
        (sigma: value_context)
        (gamma: wire context) (t: Typedterm.t) =
    let (gamma_in_box, i_enter_box) = enter_box gamma in
    let (w_t, i_t) = compile ((c, a) :: sigma) gamma_in_box t in
    let w = fresh_wire () in
    (w, Door(flip w_t, w) :: i_t @ i_enter_box)
  in
  let w, is = compile sigma gamma t in
  { output = w; instructions = is }

(*
 * Typing of circuits
 *)

type leq_constraint = {
  lower: Basetype.t;
  upper: Basetype.t
}

let solve_constraints (ineqs: leq_constraint list) : unit =
  let cmp a b = Int.compare
                  (Basetype.repr_id a)
                  (Basetype.repr_id b) in
  if !Opts.verbose then
    begin
      Printf.printf "Solving constraints:\n";
      List.iter ineqs
        ~f:(fun c -> Printf.printf "  %s <= %s\n"
                       (Printing.string_of_basetype c.lower)
                       (Printing.string_of_basetype c.upper))
    end;
  (* Turn all encoding type upper bounds into type variables. *)
  List.iter ineqs
    ~f:(fun c -> 
      match Basetype.case c.upper with
      | Basetype.Sgn (Basetype.EncodedB alpha) -> 
        Basetype.replace_by c.upper alpha
      | _ -> ());
  (* All inequalities have the form A <= alpha for some variable alpha.
   * Gather now all constraints A1 <= alpha, ..., An <= alpha for each
   * variable alpha in the form [A1,...,An] <= alpha. *)
  let joined_lower_bounds =
    ineqs
    |> List.sort ~cmp:(fun c1 c2 -> cmp c1.upper c2.upper)
    |> List.group ~break:(fun c1 c2 -> cmp c1.upper c2.upper <> 0)
    |> List.map
         ~f:(function
           | [] -> assert false
           | c :: rest ->
             (* lower bounds *)
             let bs = List.map (c :: rest) ~f:(fun c -> c.lower) in
             (* remove duplicates *)
             let rec dedup_quadratic bs =
               match bs with
               | [] -> []
               | b :: rest ->
                 let dedup_rest = dedup_quadratic rest in
                 if List.mem ~equal:Basetype.equals dedup_rest b
                 then dedup_rest
                 else b :: dedup_rest in
             let bs_dedup = dedup_quadratic bs in
             (bs_dedup, c.upper)) in
  let solve_ineq (xs, alpha) =
    match Basetype.case alpha with
    | Basetype.Var ->
      let fv_unique =
        List.map xs ~f:Basetype.free_vars
        |> List.concat
        |> List.dedup ~compare:cmp in
      let constraint_recursive =
        List.exists fv_unique ~f:(Basetype.equals alpha) in
      let sol =
        if List.length xs > 1 || constraint_recursive then
          begin
            let recty = Basetype.Data.fresh_id "conty" in
            let params = List.filter fv_unique
                           ~f:(fun beta -> not (Basetype.equals beta alpha)) in
            let n = List.length params in
            Basetype.Data.make recty ~param_count:n ~discriminated:false;
            let data = Basetype.newty (Basetype.DataB(recty, params)) in
            let sol =
              if constraint_recursive then
                Basetype.newty (Basetype.BoxB(data))
              else data in
            (* add constructors *)
            List.iteri xs
              ~f:(fun i -> fun b ->
                let arg_type =
                  Basetype.subst b
                    (fun beta ->
                       if Basetype.equals beta alpha then sol else beta)
                    in
                Basetype.Data.add_constructor
                  recty
                  (recty ^ "_" ^ (string_of_int i))
                  params
                  arg_type);
            if !Opts.verbose then
              Printf.printf "Declaring type:\n  %s\n" (Printing.string_of_data recty);
            sol
          end
        else
          (assert (xs <> []);
           List.hd_exn xs) in
      Basetype.unify_exn alpha sol
    | _ ->
      Printf.printf "%s\n" (Printing.string_of_basetype alpha);
      assert false
  in
  List.iter joined_lower_bounds ~f:solve_ineq

exception Not_Leq

(* If alpha <= beta then (embed alpha beta) is a corresponding
 * embedding from alpha to beta.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let embed (a: Basetype.t) (b: Basetype.t) (t: Ast.t): Ast.t =
  if Basetype.equals a b then
    t
  else
    match Basetype.case b with
    | Basetype.Sgn (Basetype.BoxB(c)) ->
      begin
        match Basetype.case c with
        | Basetype.Sgn (Basetype.DataB(id, l)) ->
          let cs = Basetype.Data.constructor_types id l in
          let rec inject l n =
            match l with
            | [] -> raise Not_Leq
            | b1 :: bs ->
              if Basetype.equals a b1 then
                let x = Ident.fresh "x" in
                Ast.mkTerm (
                  Ast.Bind(t, (Ast.PatVar(x), Ast.mkBox (Ast.mkInV id n (Ast.mkVar x))))
                )
              else
                inject bs (n + 1) in
          inject cs 0
        | _ -> raise Not_Leq
      end
    | Basetype.Sgn (Basetype.DataB(id, l)) ->
      let cs = Basetype.Data.constructor_types id l in
      let rec inject l n =
        match l with
        | [] -> raise Not_Leq
        | b1 :: bs ->
          if Basetype.equals a b1 then
            let x = Ident.fresh "x" in
            Ast.mkTerm (
              Ast.Bind(t, (Ast.PatVar(x), Ast.mkReturn (Ast.mkInV id n (Ast.mkVar x))))
            )
          else
            inject bs (n + 1) in
      inject cs 0
    | _ ->
      Printf.printf "%s <= %s\n"
        (Printing.string_of_basetype a)
        (Printing.string_of_basetype b);
      raise Not_Leq

(* If alpha <= beta then (embed alpha beta) is a corresponding
 * embedding from beta to alpha. The functions (embed a b) and
 * (project a b)form a section-retraction pair.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let project (a: Basetype.t) (b: Basetype.t) (t : Ast.t) : Ast.t =
  let select id params x =
    let cs = Basetype.Data.constructor_types id params in
    let rec sel cs n =
      match cs with
      | [] ->
        raise Not_Leq
      | c1 :: rest ->
        if Basetype.equals a c1 then
          Ast.mkReturn (Ast.mkTerm (Ast.SelectV(id, params, Ast.mkVar x, n)))
        else
          sel rest (n + 1) in
    sel cs 0 in
  if Basetype.equals a b then
    t
  else
    match Basetype.case b with
    | Basetype.Sgn (Basetype.BoxB(c)) ->
      begin
        match Basetype.case c with
        | Basetype.Sgn (Basetype.DataB(id, params)) ->
          let x = Ident.fresh "x" in
          let y = Ident.fresh "y" in
          let t1 = select id params x in
          let t2 = Ast.mkTerm (Ast.Bind(Ast.mkUnbox (Ast.mkVar y),
                                           (Ast.PatVar x, t1))) in
          let t3 = Ast.mkTerm (Ast.Bind(t, (Ast.PatVar y, t2))) in
          t3
        | _ -> raise Not_Leq
      end
    | Basetype.Sgn (Basetype.DataB(id, params)) ->
      let x = Ident.fresh "x" in
      let t1 = select id params x in
      let t2 = Ast.mkTerm (Ast.Bind(t, (Ast.PatVar x, t1))) in
      t2
    | _ -> raise Not_Leq


(*
 * Infers types in the string diagram and instantiated the
 * terms in the Der- and Base-nodes so that the pre_term
 * computed below will in fact be a proper term and we
 * won't have to run type inference on it.
 *
 * Inequality constraints are solved *after* all other equality constraints are
 * solved. This corresponds to first computing the constraints that the rules
 * impose locally and then connecting them with the inequality constraints.
 *
 * TODO: There should be enough type information during circuit generation
 * that this isn't necessary.
*)
let infer_types (c : t) : unit =
  let rec type_of_context (gamma: Basetype.t context): Basetype.t =
    match gamma with
    | [] -> Basetype.newvar()
    | (_, a) :: rest ->
      Basetype.newty (Basetype.PairB(type_of_context rest, a)) in
  let constraints (i: instruction)
    : leq_constraint list  =
    match i with
    | Base(w1, (s, f)) ->
      let sigma = type_of_context s in
      let unitB = Basetype.newty Basetype.UnitB in
      let beta =
        match Type.case f.Typedterm.t_type with
        | Type.Sgn (Type.Base beta) -> beta
        | _ -> assert false in
      Basetype.unify_exn w1.type_back (tensor sigma unitB);
      Basetype.unify_exn w1.type_forward (tensor sigma beta);
      []
    | Encode(w1) ->
      let sigma = Basetype.newvar() in
      let alpha = Basetype.newvar() in
      let beta = Basetype.newvar() in
      let unitB = Basetype.newty Basetype.UnitB in
      Basetype.unify_exn w1.type_back (tensor sigma (tensor alpha unitB));
      Basetype.unify_exn w1.type_forward (tensor sigma beta);
      [ {lower = alpha; upper = beta} ]
    | Decode(w1) ->
      let sigma = Basetype.newvar() in
      let alpha = Basetype.newvar() in
      let beta = Basetype.newvar() in
      let unitB = Basetype.newty Basetype.UnitB in
      Basetype.unify_exn w1.type_back (tensor sigma (tensor alpha unitB));
      Basetype.unify_exn w1.type_forward (tensor sigma beta);
      { lower = beta; upper = alpha } ::
      []
    | Tensor(w1, w2, w3) ->
      let sigma1 = Basetype.newvar() in
      let alpha1 = Basetype.newvar() in
      let beta1 = Basetype.newvar() in
      Basetype.unify_exn
        w3.type_forward (tensor sigma1 (sum alpha1 beta1));
      Basetype.unify_exn
        w1.type_back (tensor sigma1 alpha1);
      Basetype.unify_exn
        w2.type_back (tensor sigma1 beta1);
      let sigma2 = Basetype.newvar() in
      let alpha2 = Basetype.newvar() in
      let beta2 = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward (tensor sigma2 alpha2);
      Basetype.unify_exn
        w2.type_forward (tensor sigma2 beta2);
      Basetype.unify_exn
        w3.type_back (tensor sigma2 (sum alpha2 beta2));
      []
    | Der(w1, w2, (s, f)) ->
      let sigma1 = Basetype.newvar() in
      let alpha1 = Basetype.newvar() in
      let beta1 = Basetype.newvar() in
      Basetype.unify_exn
        w2.type_forward (tensor sigma1 beta1);
      Basetype.unify_exn
        w1.type_back (tensor sigma1 (tensor alpha1 beta1));
      let sigma2 = type_of_context s in
      let alpha2 = Basetype.newvar() in
      let tyf = f.Typedterm.value_type in
      Basetype.unify_exn
        w1.type_forward (tensor sigma2 (tensor tyf alpha2));
      Basetype.unify_exn
        w2.type_back (tensor sigma2 alpha2);
      []
    | App(w1(* (A => X)^* *), (s, f), w2 (* X *)) ->
      let sigma1 = Basetype.newvar() in
      let beta1 = Basetype.newvar() in
      Basetype.unify_exn
        w2.type_forward (tensor sigma1 beta1);
      Basetype.unify_exn
        w1.type_back (tensor sigma1 beta1);
      let sigma2 = type_of_context s in
      let alpha2 = Basetype.newvar() in
      let tyf = f.Typedterm.value_type in
      Basetype.unify_exn
        w1.type_forward (tensor sigma2 (tensor tyf alpha2));
      Basetype.unify_exn
        w2.type_back (tensor sigma2 alpha2);
      []
    | Case(id, params, w1 (* \Tens{A+B} X *), ws) ->
      (*let n = Basetype.Data.params id in*)
      let data = Basetype.newty (Basetype.DataB(id, params)) in
      let conss = Basetype.Data.constructor_types id params in
      let sigma1 = Basetype.newvar() in
      let gamma1 = Basetype.newvar() in
      let gamma2 = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward
        (tensor sigma1 (tensor data gamma1));
      Basetype.unify_exn
        w1.type_back
        (tensor sigma1 (tensor data gamma2));
      (List.iter ~f:(fun (w, alpha) ->
         Basetype.unify_exn
           w.type_back (tensor sigma1 (tensor alpha gamma1)))
         (List.zip_exn ws conss));
      (List.iter ~f:(fun (w, alpha) ->
         Basetype.unify_exn
           w.type_forward (tensor sigma1 (tensor alpha gamma2)))
         (List.zip_exn ws conss));
      []
    | Door(w1 (* X *) , w2 (* \Tens A X *)) ->
      let sigma1 = Basetype.newvar() in
      let alpha1 = Basetype.newvar() in
      let beta1 = Basetype.newvar() in
      Basetype.unify_exn
        w2.type_forward (tensor sigma1 (tensor alpha1 beta1));
      Basetype.unify_exn
        w1.type_back
        (tensor (tensor sigma1 alpha1) beta1);
      let sigma2 = Basetype.newvar() in
      let alpha2 = Basetype.newvar() in
      let beta2 = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward
        (tensor (tensor sigma2 alpha2) beta2);
      Basetype.unify_exn
        w2.type_back
        (tensor sigma2 (tensor alpha2 beta2));
      []
    | Assoc(w1 (* \Tens (A x B) X *), w2 (* \Tens A (\Tens B X) *)) ->
      let sigma1 = Basetype.newvar() in
      let alpha1 = Basetype.newvar() in
      let beta1 = Basetype.newvar() in
      let gamma1 = Basetype.newvar() in
      Basetype.unify_exn
        w2.type_forward
        (tensor sigma1 (tensor alpha1 (tensor beta1 gamma1)));
      Basetype.unify_exn
        w1.type_back
        (tensor sigma1 (tensor (tensor alpha1 beta1) gamma1));
      let sigma2 = Basetype.newvar() in
      let alpha2 = Basetype.newvar() in
      let beta2 = Basetype.newvar() in
      let gamma2 = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward
        (tensor sigma2 (tensor (tensor alpha2 beta2) gamma2));
      Basetype.unify_exn
        w2.type_back
        (tensor sigma2 (tensor alpha2 (tensor beta2 gamma2)));
      []
    | Direct(w1 (* (X- => T X+)* *), w2 (* X *)) ->
      let one = Basetype.newty Basetype.UnitB in
      let sigma = Basetype.newvar() in
      let betam = Basetype.newvar() in
      let betap = Basetype.newvar() in
      Basetype.unify_exn w2.type_back (tensor sigma betam);
      Basetype.unify_exn w1.type_forward (tensor sigma (tensor betam one));
      Basetype.unify_exn w1.type_back (tensor sigma betap);
      Basetype.unify_exn w2.type_forward (tensor sigma betap);
      []
    | Bind(w1 (* \Tens A X *), w2 (* A => X *)) ->
      let sigma = Basetype.newvar() in
      let alpha = Basetype.newvar() in
      let betam = Basetype.newvar() in
      let betap = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward (tensor sigma (tensor alpha betam));
      Basetype.unify_exn
        w1.type_back (tensor sigma (tensor alpha betap));
      Basetype.unify_exn
        w2.type_forward (tensor sigma betap);
      Basetype.unify_exn
        w2.type_back (tensor sigma (tensor alpha betam));
      []
    | LWeak(w1 (* \Tens A X*), w2 (* \Tens B X*)) (* B <= A *) ->
      let sigma = Basetype.newvar() in
      let alpha = Basetype.newvar() in
      let beta = Basetype.newvar() in
      let gamma1 = Basetype.newvar() in
      let gamma2 = Basetype.newvar() in
      Basetype.unify_exn
        w1.type_forward (tensor sigma (tensor alpha gamma1));
      Basetype.unify_exn
        w1.type_back (tensor sigma (tensor alpha gamma2));
      Basetype.unify_exn
        w2.type_forward (tensor sigma (tensor beta gamma2));
      Basetype.unify_exn
        w2.type_back (tensor sigma (tensor beta gamma1));
      [ {lower = beta; upper = alpha} ]
    | Seq(w1 (* (T A)^* *), w2 (* (\Tens A (TB))^* *), w3 (* TB *)) ->
      let one = Basetype.newty Basetype.UnitB in
      let sigma = Basetype.newvar() in
      let alpha = Basetype.newvar() in
      let beta = Basetype.newvar() in
      Basetype.unify_exn w1.type_forward (tensor sigma one);
      Basetype.unify_exn w1.type_back (tensor sigma alpha);
      Basetype.unify_exn w2.type_forward (tensor sigma (tensor alpha one));
      Basetype.unify_exn w2.type_back (tensor sigma (tensor alpha beta));
      Basetype.unify_exn w3.type_forward (tensor sigma beta);
      Basetype.unify_exn w3.type_back (tensor sigma one);
      [] in
  try
    let constraints = List.concat_map ~f:constraints c.instructions in
    solve_constraints constraints
  with
  | Uftype.Constructor_mismatch
  | Uftype.Cyclic_type ->
    failwith "Internal error: cannot unify constraints in compilation"

let of_typedterm (t : Typedterm.t) : t =
  try
    let c = raw_circuit_of_term [] [] t in
    ignore(infer_types c);
    c
  with
  | Uftype.Constructor_mismatch
  | Uftype.Cyclic_type ->
    raise (Typing_error(None, "Cannot unify index types: invalid direct definition."))

(* TODO: This function should be cleaned up *)
let dot_of_circuit
      ?title:(title = "")
      ?wire_style:(wire_style = fun _ -> "")
      (c: t) : string =
  let node_name ins =
    match ins with
    | Base(w1, _) ->
      Printf.sprintf "\"Base({%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
    | Encode(w1) ->
      Printf.sprintf "\"Encode({%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
    | Decode(w1) ->
      Printf.sprintf "\"Decode({%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
    | Tensor(w1, w2, w3) ->
      Printf.sprintf "\"Tensor({%s,%s},{%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
        (Ident.to_string w3.src) (Ident.to_string w3.dst)
    | Der(w1, w2, _) ->
      Printf.sprintf "\"Der({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | Case(id, _, w1, ws) ->
      Printf.sprintf "\"Case(%s, {%s,%s},%s)\""
        id (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (String.concat ~sep:","
           (List.map ~f:(fun w -> Printf.sprintf "{%s,%s}"
                                    (Ident.to_string w.src)
                                    (Ident.to_string w.dst)) ws))
    | Door(w1, w2) ->
      Printf.sprintf "\"Door({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | Assoc(w1, w2) ->
      Printf.sprintf "\"Assoc({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | LWeak(w1, w2) ->
      Printf.sprintf "\"LWeak({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | Bind(w1, w2) ->
      Printf.sprintf "\"Bind({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | App(w1, _, w2) ->
      Printf.sprintf "\"App({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | Direct(w1, w2) ->
      Printf.sprintf "\"Direct({%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
    | Seq(w1, w2, w3) ->
      Printf.sprintf "\"Seq({%s,%s},{%s,%s},{%s,%s})\""
        (Ident.to_string w1.src) (Ident.to_string w1.dst)
        (Ident.to_string w2.src) (Ident.to_string w2.dst)
        (Ident.to_string w3.src) (Ident.to_string w3.dst)
  in
  let entry_label = Ident.fresh "wentry" in
  let exit_label = Ident.fresh "wexit" in
  let node_label ins =
    let ws = wires ins in
    let name =
      match ins with
      | Base _ -> "base(...)"
      | Encode _ -> "encode(...)"
      | Decode _ -> "decode(...)"
      | Tensor _ -> "&otimes;"
      | Der _ -> "&pi;_..."
      | Case _ -> "case"
      | Door(_, w) ->
        if w.src = entry_label then "\", shape=\"plaintext" else "&uarr;"
      | Assoc _ -> "assoc;"
      | LWeak _ -> "lweak"
      | Bind _ -> "bind"
      | Seq _ -> "seq"
      | App _ -> "app"
      | Direct _ -> "direct"
    in
    List.fold_right ws
      ~f:(fun w s -> Printf.sprintf "%s(%s)" s (Ident.to_string w.src))
      ~init:name
  in
  let instructions_with_result =
    (Door(flip c.output,
          { src = entry_label;
            dst = exit_label;
            type_forward = Basetype.newvar();
            type_back = Basetype.newvar()})) :: c.instructions in
  let node_map_by_src =
    let rec build_dst_map i =
      match i with
      | [] -> Ident.Map.empty
      | node :: rest ->
        List.fold_right (wires node)
          ~f:(fun w map -> Ident.Map.add map ~key:w.src ~data:node)
          ~init:(build_dst_map rest)
    in build_dst_map instructions_with_result in
  let buf = Buffer.create 1024 in
  let nodes () =
    List.iter instructions_with_result
      ~f:(fun ins ->
        Buffer.add_string buf (node_name ins);
        Buffer.add_string buf "[label=\"";
        Buffer.add_string buf (node_label ins);
        Buffer.add_string buf "\"];\n");
  in
  let edges () =
    let edge srcins (w: wire) =
      try
        let dstins = Ident.Map.find_exn node_map_by_src w.dst in
        Buffer.add_string buf (node_name srcins);
        Buffer.add_string buf " -> ";
        Buffer.add_string buf (node_name dstins);
        Buffer.add_string buf (wire_style w);
        Buffer.add_string buf
          (Printf.sprintf "[label=\"%s(%s)\"]" (Ident.to_string w.dst)
             (Printing.string_of_basetype w.type_forward));
        Buffer.add_string buf ";\n ";
      with Not_found -> () (* Weakening *) in
    List.iter instructions_with_result
      ~f:(fun srcins -> List.iter ~f:(edge srcins) (wires srcins))
  in
  Buffer.add_string buf "digraph G {\n labelloc=t; label=\"";
  Buffer.add_string buf title;
  Buffer.add_string buf "\";fontname=Monospace;fontcolor=blue;fontsize=36;";
  nodes ();
  edges ();
  Buffer.add_string buf "}";
  Buffer.contents buf
