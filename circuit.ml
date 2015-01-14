(** Compilation to circuits
  * TODO:
  *  - simplify boilerplate
  *  - construct circuit with the correct types right away,
  *    without using type inference
*)
open Core.Std
open Unify
open Typing

(** A wire represents a dart in an undirected graph. *)
type wire = {
  src: int;
  dst: int;
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

type t =
    { output : wire;
      instructions : instruction list
    }

let map_wires_instruction (f: wire -> wire): instruction -> instruction =
  fun i ->
    match i with
    | Base(w, t) -> Base(f w, t)
    | Encode(w) -> Encode(f w)
    | Decode(w) -> Decode(f w)
    | Tensor(w1, w2, w3) -> Tensor(f w1, f w2, f w3)
    | Der(w1, w2, t) -> Der(f w1, f w2, t)
    | Case(id, params, w1, ws) -> Case(id, params, f w1, List.map ~f:f ws)
    | Door(w1, w2) -> Door(f w1, f w2)
    | Assoc(w1, w2) -> Assoc(f w1, f w2)
    | LWeak(w1, w2) -> LWeak(f w1, f w2)
    | Bind(w1, w2) -> Bind(f w1, f w2)
    | Seq(w1, w2, w3) -> Seq(f w1, f w2, f w3)
    | App(w1, t, w2) -> App(f w1, t, f w2)
    | Direct(w1, w2) -> Direct(f w1, f w2)

let wires (i: instruction) : wire list =
  let ws = ref [] in
  let f w = ws := w :: !ws; w in
  ignore (map_wires_instruction f i);
  !ws

(* Wires for all the variables in the context.
 * They point into the graph with their dst-label. *)

module U = Unify(struct type t = unit end)

let tensor s t = Basetype.newty (Basetype.PairB(s, t))
let sum s t = Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [s; t]))

(**
  * Compilation of an upper-level term to a string diagram.
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
  * - The diagram as a list of instructions.
  *)
(* ASSUMPTION: all type annotations in t may only contain index types
 * that are variables, i.e. not {1+1}'a --o 'b, for example. *)
let raw_circuit_of_term  (sigma: value_context) (gamma: wire context)
      (t: Typedterm.t): t =
  let used_wirenames =
    List.fold_right gamma ~f:(fun (_, w) wns -> w.src :: w.dst :: wns) ~init:[] in
  let next_wirename = ref ((List.fold_right used_wirenames ~f:max ~init:(-1)) + 1) in
  let restrict_context gamma t =
    List.filter gamma
      ~f:(fun (x, _) -> List.Assoc.mem t.Typedterm.t_context x) in
  let remove_context gamma ls =
    List.filter gamma ~f:(fun (x, _) -> not (List.mem ls x)) in
  let fresh_wire () =
    let n = !next_wirename in
    next_wirename := !next_wirename + 2;
    { src = n;
      dst = n + 1;
      type_forward = Basetype.newty Basetype.Var;
      type_back = Basetype.newty Basetype.Var
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
    | Typedterm.Return(v) ->
      let w = fresh_wire () in
      let s = Basetype.newty Basetype.Var in
      let one = Basetype.newty Basetype.UnitB in
      U.unify w.type_back (tensor s one);
      U.unify w.type_forward (tensor s v.Typedterm.value_type);
      w, [Base(w, (sigma, t))]
    | Typedterm.Direct(ty, t) ->
      let tym, typ = Type.question_answer_pair ty in
      let w_t, i_t = compile sigma gamma t in
      let w = fresh_wire () in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w.type_back (tensor sigma tym);
      U.unify w.type_forward (tensor sigma typ);
      w, Direct(flip w_t, w) :: i_t
    | Typedterm.AppV(s, v) ->
      let wr = fresh_wire () in
      let w_s, i_s = compile sigma gamma s in
      wr, App(flip w_s, (sigma, v), wr) :: i_s
    | Typedterm.AppI(s, t) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = restrict_context gamma t in
      let w_s, i_s = compile sigma gamma_s s in
      let alpha = Basetype.newtyvar() in
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
      let w_s, i_s = compile sigma gamma_s_inbox s in
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
      let alpha = Basetype.newtyvar() in
      let w_s, i_s =
        compile_in_box (Ident.fresh "unused", alpha) sigma gamma_s s in
      let delta  = List.map ~f:(fun x -> (x, fresh_wire())) xs in
      let ws = List.map ~f:(fun (_, w) -> w) delta in
      let w_types = List.map ~f:(fun _ -> Basetype.newtyvar()) ws in
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
      let sigmaty = Basetype.newty Basetype.Var in
      let qty = Basetype.newty Basetype.Var in
      let data = Basetype.newty (Basetype.DataB(id, params)) in
      U.unify w_join.type_back (tensor sigmaty (tensor data qty));
      let w = fresh_wire () in
      let i_der = [Der(flip w_join, w, (sigma, f))] in
      (w, i_der @ i_join @ i_leavebox @ i_ts @ i_dup)
    | Typedterm.Fun((x, a, ty), s) ->
      let tym, typ = Type.question_answer_pair ty in
      let sigma1 = Basetype.newty Basetype.Var in
      let sigma2 = Basetype.newty Basetype.Var in
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
      let sigmat = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      U.unify w_t.type_back (tensor sigmat (tensor a beta));
      let w = fresh_wire () in
      w, Bind(flip w_t, w) :: i_t
    | Typedterm.Bind((s, a), (c, t)) ->
      let gamma_s = restrict_context gamma s in
      let gamma_t = restrict_context gamma t in
      let wr = fresh_wire () in
      let w_s, i_s = compile sigma gamma_s s in
      let w_t, i_t = compile_in_box (c, a) sigma gamma_t t in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w_s.type_forward (tensor sigma a); (* TODO *)
      wr, Seq(flip w_s, flip w_t, wr) ::
          i_s @ i_t
    | Typedterm.Const(Ast.Cencode(a, b)) ->
      let w = fresh_wire () in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w.type_back (tensor sigma a);
      U.unify w.type_forward (tensor sigma b);
      w, [Encode(w)]
    | Typedterm.Const(Ast.Cdecode(a, b)) ->
      let w = fresh_wire () in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w.type_back (tensor sigma a);
      U.unify w.type_forward (tensor sigma b);
      w, [Decode(w)]
    | Typedterm.Const(_) ->
      let w = fresh_wire () in
      let w1 = fresh_wire () in
      let w2 = fresh_wire () in
      let xv = Ident.fresh "x" in
      let x, a, b =
        match Type.finddesc t.Typedterm.t_type with
        | Type.FunV(a, b) ->
          { Typedterm.value_desc = Typedterm.VarV xv;
            Typedterm.value_type = a;
            Typedterm.value_loc = Ast.Location.none },
          a, b
        | _ ->
          assert false in
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

type type_constraint =
  | Eq of U.type_eq
  | LEq of Basetype.t * Basetype.t

let beq_constraint expected_ty actual_ty =
  Eq (U.Basetype_eq(expected_ty, actual_ty, None))
let leq_constraint a b =
  LEq (a, b)

let solve_constraints (con: type_constraint list) : unit =
  (* separate context in inequalities and equalities *)
  let rec separate con ineqs eqs =
    begin
      match con with
      | [] -> ineqs, eqs
      | LEq(t, t') :: con' ->
        separate con' ((t, t') :: ineqs) eqs
      | Eq(e) :: con' ->
        separate con' ineqs  (e :: eqs)
    end in
  let ineqs, eqs = separate con [] [] in
  (* unify equations first *)
  U.unify_eqs eqs;
  let cmp a b = Int.compare
                  (Basetype.find a).Basetype.id
                  (Basetype.find b).Basetype.id in
  (* All inequalities have the form A <= alpha for some variable alpha.
   * Gather now all constraints A1 <= alpha, ..., An <= alpha for each
   * variable alpha in the form [A1,...,An] <= alpha. *)
  let joined_lower_bounds =
    ineqs
    |> List.sort ~cmp:(fun (_, a) (_, b) -> cmp a b)
    |> List.group ~break:(fun (_, a) (_, b) -> cmp a b <> 0)
    |> List.map
         ~f:(function
           | [] -> assert false
           | (b, a)::rest ->
             let bs, _ = List.unzip rest in
             (b :: bs, a)) in
  let solve_ineq (xs, alpha) =
    match Basetype.finddesc alpha with
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
            Basetype.Data.make recty ~nparams:n ~discriminated:false;
            let data = Basetype.newty (Basetype.DataB(recty, params)) in
            let sol =
              if constraint_recursive then
                Basetype.newty (Basetype.BoxB(data))
              else data in
            (* add constructors *)
            List.iteri xs
              ~f:(fun i -> fun b ->
                let arg_type =
                  Basetype.subst
                    (fun beta ->
                       if Basetype.equals beta alpha then sol else beta)
                    b in
                Basetype.Data.add_constructor
                  recty
                  (recty ^ "_" ^ (string_of_int i))
                  params
                  arg_type);
            sol
          end
        else
          (assert (xs <> []);
           List.hd_exn xs) in
      U.unify_eqs [U.Basetype_eq(sol, alpha, None)]
    | _ ->
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
    match Basetype.finddesc b with
    | Basetype.BoxB(c) ->
      begin
        match Basetype.finddesc c with
        | Basetype.DataB(id, l) ->
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
    | Basetype.DataB(id, l) ->
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
    | _ -> raise Not_Leq

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
    match Basetype.finddesc b with
    | Basetype.BoxB(c) ->
      begin
        match Basetype.finddesc c with
        | Basetype.DataB(id, params) ->
          let x = Ident.fresh "x" in
          let y = Ident.fresh "y" in
          let t1 = select id params x in
          let t2 = Ast.mkTerm (Ast.Bind(Ast.mkUnbox (Ast.mkVar y),
                                           (PatVar x, t1))) in
          let t3 = Ast.mkTerm (Ast.Bind(t, (PatVar y, t2))) in
          t3
        | _ -> raise Not_Leq
      end
    | Basetype.DataB(id, params) ->
      let x = Ident.fresh "x" in
      let t1 = select id params x in
      let t2 = Ast.mkTerm (Ast.Bind(t, (PatVar x, t1))) in
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
    | [] -> Basetype.newtyvar()
    | (_, a) :: rest ->
      Basetype.newty (Basetype.PairB(type_of_context rest, a)) in
  let rec constraints (instructions: instruction list)
    : type_constraint list  =
    match instructions with
    | [] -> []
    | Base(w1, (s, f))::rest ->
      let sigma = type_of_context s in
      let one = Basetype.newty Basetype.UnitB in
      let beta =
        match Type.finddesc f.Typedterm.t_type with
        | Type.Base beta -> beta
        | _ -> assert false in
      beq_constraint w1.type_back (tensor sigma one) ::
      beq_constraint w1.type_forward (tensor sigma beta) ::
      (constraints rest)
    | Encode(w1)::rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      beq_constraint w1.type_back (tensor sigma alpha) ::
      beq_constraint w1.type_forward (tensor sigma beta) ::
      leq_constraint alpha beta ::
      (constraints rest)
    | Decode(w1)::rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      beq_constraint w1.type_back (tensor sigma alpha) ::
      beq_constraint w1.type_forward (tensor sigma beta) ::
      leq_constraint beta alpha ::
      (constraints rest)
    | Tensor(w1, w2, w3)::rest ->
      let sigma1 = Basetype.newty Basetype.Var in
      let alpha1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint
        w3.type_forward (tensor sigma1 (sum alpha1 beta1)) ::
      beq_constraint
        w1.type_back (tensor sigma1 alpha1) ::
      beq_constraint
        w2.type_back (tensor sigma1 beta1) ::
      let sigma2 = Basetype.newty Basetype.Var in
      let alpha2 = Basetype.newty Basetype.Var in
      let beta2 = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward (tensor sigma2 alpha2) ::
      beq_constraint
        w2.type_forward (tensor sigma2 beta2) ::
      beq_constraint
        w3.type_back (tensor sigma2 (sum alpha2 beta2)) ::
      (constraints rest)
    | Der(w1, w2, (s, f))::rest ->
      let sigma1 = type_of_context s in
      let alpha1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint
        w2.type_forward (tensor sigma1 beta1) ::
      beq_constraint
        w1.type_back (tensor sigma1 (tensor alpha1 beta1)) ::
      let sigma2 = Basetype.newty Basetype.Var in
      let alpha2 = Basetype.newty Basetype.Var in
      let tyf = f.Typedterm.value_type in
      beq_constraint
        w1.type_forward (tensor sigma2 (tensor tyf alpha2)) ::
      beq_constraint
        w2.type_back (tensor sigma2 alpha2) ::
      (constraints rest)
    | App(w1(* (A => X)^* *), (s, f), w2 (* X *))::rest ->
      let sigma1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint
        w2.type_forward (tensor sigma1 beta1) ::
      beq_constraint
        w1.type_back (tensor sigma1 beta1) ::
      let sigma2 = type_of_context s in
      let alpha2 = Basetype.newty Basetype.Var in
      let tyf = f.Typedterm.value_type in
      beq_constraint
        w1.type_forward (tensor sigma2 (tensor tyf alpha2)) ::
      beq_constraint
        w2.type_back (tensor sigma2 alpha2) ::
      (constraints rest)
    | Case(id, params, w1 (* \Tens{A+B} X *), ws) :: rest ->
      (*let n = Basetype.Data.params id in*)
      let data = Basetype.newty (Basetype.DataB(id, params)) in
      let conss = Basetype.Data.constructor_types id params in
      let sigma1 = Basetype.newty Basetype.Var in
      let gamma1 = Basetype.newty Basetype.Var in
      let gamma2 = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward
        (tensor sigma1 (tensor data gamma1)) ::
      beq_constraint
        w1.type_back
        (tensor sigma1 (tensor data gamma2)) ::
      (List.map ~f:(fun (w, alpha) ->
         beq_constraint
           w.type_back (tensor sigma1 (tensor alpha gamma1)))
         (List.zip_exn ws conss)) @
      (List.map ~f:(fun (w, alpha) ->
         beq_constraint
           w.type_forward (tensor sigma1 (tensor alpha gamma2)))
         (List.zip_exn ws conss)) @
      (constraints rest)
    | Door(w1 (* X *) , w2 (* \Tens A X *))::rest ->
      let sigma1 = Basetype.newty Basetype.Var in
      let alpha1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint
        w2.type_forward (tensor sigma1 (tensor alpha1 beta1)) ::
      beq_constraint
        w1.type_back
        (tensor (tensor sigma1 alpha1) beta1) ::
      let sigma2 = Basetype.newty Basetype.Var in
      let alpha2 = Basetype.newty Basetype.Var in
      let beta2 = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward
        (tensor (tensor sigma2 alpha2) beta2) ::
      beq_constraint
        w2.type_back
        (tensor sigma2 (tensor alpha2 beta2)) ::
      (constraints rest)
    | Assoc(w1 (* \Tens (A x B) X *), w2 (* \Tens A (\Tens B X) *))::rest ->
      let sigma1 = Basetype.newty Basetype.Var in
      let alpha1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      let gamma1 = Basetype.newty Basetype.Var in
      beq_constraint
        w2.type_forward
        (tensor sigma1 (tensor alpha1 (tensor beta1 gamma1))) ::
      beq_constraint
        w1.type_back
        (tensor sigma1 (tensor (tensor alpha1 beta1) gamma1)) ::
      let sigma2 = Basetype.newty Basetype.Var in
      let alpha2 = Basetype.newty Basetype.Var in
      let beta2 = Basetype.newty Basetype.Var in
      let gamma2 = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward
        (tensor sigma2 (tensor (tensor alpha2 beta2) gamma2)) ::
      beq_constraint
        w2.type_back
        (tensor sigma2 (tensor alpha2 (tensor beta2 gamma2))) ::
      (constraints rest)
    | Direct(w1 (* (X- => T X+)* *), w2 (* X *))::rest ->
      let sigma = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint w2.type_forward (tensor sigma beta1) ::
      beq_constraint w1.type_back (tensor sigma beta1) ::
      let beta2 = Basetype.newty Basetype.Var in
      let one = Basetype.newty Basetype.UnitB in
      beq_constraint
        w1.type_forward
        (tensor sigma (tensor beta2 one)) ::
      beq_constraint
        w2.type_back
        (tensor sigma beta2) ::
      (constraints rest)
    | Bind(w1 (* \Tens A X *), w2 (* A => X *)) :: rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let betam = Basetype.newty Basetype.Var in
      let betap = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward (tensor sigma (tensor alpha betam)) ::
      beq_constraint
        w1.type_back (tensor sigma (tensor alpha betap)) ::
      beq_constraint
        w2.type_forward (tensor sigma betap) ::
      beq_constraint
        w2.type_back (tensor sigma (tensor alpha betam)) ::
      (constraints rest)
    | LWeak(w1 (* \Tens A X*), w2 (* \Tens B X*)) (* B <= A *)::rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      let gamma1 = Basetype.newty Basetype.Var in
      let gamma2 = Basetype.newty Basetype.Var in
      beq_constraint
        w1.type_forward (tensor sigma (tensor alpha gamma1)) ::
      beq_constraint
        w1.type_back (tensor sigma (tensor alpha gamma2)) ::
      beq_constraint
        w2.type_forward (tensor sigma (tensor beta gamma2)) ::
      beq_constraint
        w2.type_back (tensor sigma (tensor beta gamma1)) ::
      leq_constraint beta alpha ::
      (constraints rest)
    | Seq(w1 (* (T A)^* *), w2 (* (\Tens A (TB))^* *), w3 (* TB *)) :: rest ->
      let one = Basetype.newty Basetype.UnitB in
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      beq_constraint w1.type_forward (tensor sigma one) ::
      beq_constraint w1.type_back (tensor sigma alpha) ::
      beq_constraint w2.type_forward (tensor sigma (tensor alpha one)) ::
      beq_constraint w2.type_back (tensor sigma (tensor alpha beta)) ::
      beq_constraint w3.type_forward (tensor sigma beta) ::
      beq_constraint w3.type_back (tensor sigma one) ::
      (constraints rest) in
  try
    let cs = constraints c.instructions in
    solve_constraints cs;
  with
  | U.Not_Unifiable _ ->
    failwith "Internal error: cannot unify constraints in compilation"

let of_typedterm (t : Typedterm.t) : t =
  try
    let c = raw_circuit_of_term [] [] t in
    ignore(infer_types c);
    c
  with
  | U.Not_Unifiable _ ->
    raise (Typing_error(None, "Cannot unify index types: invalid direct definition."))

(* TODO: This function should be cleaned up *)
let dot_of_circuit
      ?title:(title = "")
      ?wire_style:(wire_style = fun _ -> "")
      (c: t) : string =
  let node_name ins =
    match ins with
    | Base(w1, _) ->
      Printf.sprintf "\"Base({%i,%i})\"" w1.src w1.dst
    | Encode(w1) ->
      Printf.sprintf "\"Encode({%i,%i})\"" w1.src w1.dst
    | Decode(w1) ->
      Printf.sprintf "\"Decode({%i,%i})\"" w1.src w1.dst
    | Tensor(w1, w2, w3) ->
      Printf.sprintf "\"Tensor({%i,%i},{%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst w3.src w3.dst
    | Der(w1, w2, _) ->
      Printf.sprintf "\"Der({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | Case(id, _, w1, ws) ->
      Printf.sprintf "\"Case(%s, {%i,%i},%s)\""
        id w1.src w1.dst
        (String.concat ~sep:","
           (List.map ~f:(fun w -> Printf.sprintf "{%i,%i}" w.src w.dst) ws))
    | Door(w1, w2) ->
      Printf.sprintf "\"Door({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | Assoc(w1, w2) ->
      Printf.sprintf "\"Assoc({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | LWeak(w1, w2) ->
      Printf.sprintf "\"LWeak({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | Bind(w1, w2) ->
      Printf.sprintf "\"Bind({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | App(w1, _, w2) ->
      Printf.sprintf "\"App({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | Direct(w1, w2) ->
      Printf.sprintf "\"Direct({%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst
    | Seq(w1, w2, w3) ->
      Printf.sprintf "\"Seq({%i,%i},{%i,%i},{%i,%i})\""
        w1.src w1.dst w2.src w2.dst w3.src w3.dst
  in
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
        if w.src = -1 then "\", shape=\"plaintext" else "&uarr;"
      | Assoc _ -> "assoc;"
      | LWeak _ -> "lweak"
      | Bind _ -> "bind"
      | Seq _ -> "seq"
      | App _ -> "app"
      | Direct _ -> "direct"
    in
    List.fold_right ws ~f:(fun w s -> Printf.sprintf "%s(%i)" s w.src) ~init:name
  in
  let instructions_with_result =
    (Door(flip c.output,
          { src = (-1);
            dst = (-2);
            type_forward = Basetype.newty Basetype.Var;
            type_back = Basetype.newty Basetype.Var})) :: c.instructions in
  let node_map_by_src =
    let rec build_dst_map i =
      match i with
      | [] -> Int.Map.empty
      | node :: rest ->
        List.fold_right (wires node)
          ~f:(fun w map -> Int.Map.add map ~key:w.src ~data:node)
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
        let dstins = Int.Map.find_exn node_map_by_src w.dst in
        Buffer.add_string buf (node_name srcins);
        Buffer.add_string buf " -> ";
        Buffer.add_string buf (node_name dstins);
        Buffer.add_string buf (wire_style w);
        Buffer.add_string buf
          (Printf.sprintf "[label=\"%i(%s)\"]" w.dst
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
