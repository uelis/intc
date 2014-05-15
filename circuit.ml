(** Compilation to circuits
  * TODO: canonize-annahmen
  * TODO: dokumentiere, welche terme in den Circuits vorkomment
  * koennen
  * TODO: ueberpruefe, dass die neu inferrierten typen auch mit den
  * annotationen uebereinstimmen
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
(* TODO: DOCUMENTATION
 * Graph invariant: There are no two wires with w1.src = w2.src that are affixed
 * to different nodes. I.e. w.src and w.dst are darts and must therefore be
 * unique in the graph *)

(* All wires are meant to 'leave' the instructions, i.e. they are all affixed
*  with their src-label to the instruction.
*  The type of the respective wires is indicated in the comments. *)
type instruction =
  | Axiom of wire (* fn () -> f *) * (Term.var list * (Term.var * Term.t))
  | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
  | Der of wire (* \Tens A X *) * wire (* X *) * (Term.var list * Term.t)
  | Case of Basetype.Data.id * Basetype.t list * wire * (wire list)
  | Door of wire (* X *) * wire (* \Tens A X *)
  | Assoc of wire (* \Tens (A x B) X *) * wire (* \Tens A (\Tens B X) *) 
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B <= A *)
  | Bind of wire (* (\Tens A (1 => B))^* *) * wire (* A => B *)
  | Seq of wire (* (A=>B)^* *) * wire (* (B=>C)^* *) * wire (* A=>C *)

type t = 
    { output : wire; 
      instructions : instruction list
    }

let rec wires (i: instruction list): wire list =
  match i with
    | [] -> []
    | Axiom(w1, _) :: is -> w1 :: (wires is)
    | Der(w1, w2, _) :: is | Door(w1, w2) :: is | Assoc(w1, w2) :: is 
    | LWeak(w1, w2) :: is | Bind(w1, w2) :: is ->
      w1 :: w2 :: (wires is)
    | Tensor(w1, w2, w3) :: is | Seq(w1, w2, w3) :: is ->
      w1 :: w2 :: w3 :: (wires is)
    | Case(_, _, w1, ws) :: is -> w1 :: ws @ (wires is)

let map_wires_instruction (f: wire -> wire): instruction -> instruction =
  fun i -> 
    match i with
    | Axiom(w, t) -> Axiom(f w, t)
    | Tensor(w1, w2, w3) -> Tensor(f w1, f w2, f w3)
    | Der(w1, w2, t) -> Der(f w1, f w2, t)
    | Case(id, params, w1, ws) -> Case(id, params, f w1, List.map ~f:f ws)
    | Door(w1, w2) -> Door(f w1, f w2)
    | Assoc(w1, w2) -> Assoc(f w1, f w2)
    | LWeak(w1, w2) -> LWeak(f w1, f w2)
    | Bind(w1, w2) -> Bind(f w1, f w2)
    | Seq(w1, w2, w3) -> Seq(f w1, f w2, f w3)

(* renaming of wires *)                               
let map_wire (f: int -> int): wire -> wire =
  fun w -> 
    {src = f w.src;
     dst = f w.dst;
     type_forward = w.type_forward;
     type_back = w.type_back
    }

let map_instruction (f: int -> int): instruction -> instruction =
  map_wires_instruction (map_wire f) 

(* Wires for all the variables in the context. 
 * They point into the graph with their dst-label. *)

(* TODO: canonize terms *)

module U = Unify(struct type t = unit end)

let tensor s t = Basetype.newty (Basetype.TensorW(s, t))
let sum s t = Basetype.newty (Basetype.DataW(Basetype.Data.sumid 2, [s; t]))

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
let raw_circuit_of_termU  (sigma: Term.var list) (gamma: wire context) (t: Term.t): t = 
  let used_wirenames = 
    List.fold_right gamma ~f:(fun (_, w) wns -> w.src :: w.dst :: wns) ~init:[] in 
  let next_wirename = ref ((List.fold_right used_wirenames ~f:max ~init:(-1)) + 1) in
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
      ((x, w3) :: d, LWeak(flip w, w1)::Assoc(flip w1, w2)::Door(w3, flip w2) :: i) 
  in
  let rec compile (sigma: Term.var list) (gamma: wire context) (t: Term.t) =
    match t.Term.desc with
    | Term.Var(x) ->
      if List.mem sigma x then
        begin
          let w = fresh_wire () in 
          (w, [Axiom(w, 
                     (sigma, 
                      (Term.unusable_var, Term.mkVar x)))]) 
        end
      else
        begin
          let wx = List.Assoc.find_exn gamma x in 
          let w = fresh_wire () in 
          let w' = fresh_wire () in 
          (w, [Der(flip w', w, 
                   (sigma, Term.mkUnitW));
               LWeak(flip wx, w')])
        end
    | Term.HackU(ty, t) ->
      let tym, typ = Type.question_answer_pair ty in
      let w, i = compile sigma gamma t in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w.type_back (tensor sigma tym);
      U.unify w.type_forward (tensor sigma typ);
      w, i
    | Term.App(s, a, t) ->
      begin
        match Type.finddesc a with
        | Type.FunW _ ->
          let gamma_s, gamma_t = split_context gamma s t in
          let wr = fresh_wire () in 
          let (w_s, i_s) = compile sigma gamma_s s in
          let (w_t, i_t) = compile sigma gamma_t t in
          wr, Seq(flip w_t, flip w_s, wr) :: 
              i_s @ i_t
        | Type.FunU _ ->
          let gamma_s, gamma_t = split_context gamma s t in
          let (w_s, i_s) = compile sigma gamma_s s in
          let (w_t, i_t) = compile_in_box Term.unusable_var sigma gamma_t t in
          let wr = fresh_wire () in 
          (wr, Tensor(flip w_t, wr, flip w_s) :: i_s @ i_t)
        | Type.Var | Type.Link _ -> 
          assert false
      end
    | Term.CopyU(s, (x, y, t)) ->
      let gamma_s, gamma_t = split_context gamma s t in
      let (w_s, i_s) = compile_in_box Term.unusable_var sigma gamma_s s in
      let w_x = fresh_wire () in
      let w_y = fresh_wire () in
      let (w_t, i_t) = compile sigma ((x, w_x) :: (y, w_y) :: gamma_t) t in
      (* TODO: check that types are really inferred! *)
      (w_t, Case(Basetype.Data.sumid 2, [Basetype.newtyvar(); 
                                         Basetype.newtyvar()],
                 flip w_s, [w_x; w_y]) :: i_s @ i_t)
    | Term.Case(id, params, f, ts) -> (* [(x, s); (y, t)]) when id = Type.Data.sumid 2 -> *)
      let n = List.length ts in
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
        (List.fold_right (List.zip_exn gammas ts)
           ~f:(fun (gamma, (x, t)) (ws, is) -> 
           let w', is' = compile (x :: sigma) gamma t in
           w' :: ws, is' @ is)  
           ~init:([], [])) in
      let ws = List.init n ~f:(fun _ -> fresh_wire ()) in
      let i_leavebox = List.map (List.zip_exn ts_in_box ws)
                         ~f:(fun (t, w) -> Door(flip t, w)) in
      let w_join = fresh_wire () in
      let i_join = [Case(id, params, w_join, List.map ~f:flip ws)] in
      let sigmaty = Basetype.newty Basetype.Var in
      let qty = Basetype.newty Basetype.Var in
      let data = Basetype.newty (Basetype.DataW(id, params)) in
      U.unify w_join.type_back (tensor sigmaty (tensor data qty));
      let w = fresh_wire () in
      let i_der = [Der(flip w_join, w, (sigma, f))] in
      (w, i_der @ i_join @ i_leavebox @ i_ts @ i_dup)
    | Term.LambdaU((x, a, ty), s) ->
      let tym, typ = Type.question_answer_pair ty in
      let sigma1, sigma2 = Basetype.newty Basetype.Var, Basetype.newty Basetype.Var in
      (* ASSUMPTION: all annotations must have type variables as index
       * types.
       * TODO: Give a warning otherwise! *)
      let wx = 
        { (fresh_wire ()) with 
          type_forward = tensor sigma1 (tensor a typ);
          type_back = tensor sigma2 (tensor a tym)} in 
      let w = fresh_wire () in
      let (w_s, i_s) = (compile sigma ((x, wx) :: gamma) s) in
      (w, Tensor(wx, flip w_s, w) :: i_s)
    | Term.TypeAnnot (t, ty) -> 
      let (w, ins) = compile sigma gamma t in
      let tyTensor (s, t) = Basetype.newty (Basetype.TensorW(s, t)) in
      let sigma1 = Basetype.newty Basetype.Var in
      let tym, typ = Type.question_answer_pair ty in
      U.unify w.type_forward (tyTensor(sigma1, typ));
      U.unify w.type_back (tyTensor(sigma1, tym)); 
      (w, ins)
    | Term.LambdaW((x, a), t) ->
      let w = fresh_wire () in
      let (w_t, i_t) = compile_in_box x sigma gamma t in
      let sigma = Basetype.newty Basetype.Var in
      U.unify w.type_back (tensor sigma a);
      (w, Bind(flip w_t, w) :: i_t)
    | Term.BindW((s, a), (c, t)) ->
      let gamma_s, gamma_t = split_context gamma s t in
      let wr = fresh_wire () in 
      let (w_s, i_s) = compile sigma gamma_s s in
      let (w_t, i_t) = compile_in_box c sigma gamma_t t in
      let w_t1 = fresh_wire () in 
      let sigma = Basetype.newty Basetype.Var in
      U.unify w_s.type_forward (tensor sigma a);
      wr, Bind(flip w_t, w_t1) ::
          Seq(flip w_s, flip w_t1, wr) :: 
          i_s @ i_t
    | Term.ValW _ | Term.UnitW | Term.PairW _ 
    | Term.FstW _ | Term.SndW _ | Term.Select _
    | Term.InW _ | Term.Box _ | Term.Unbox _ ->
      let w = fresh_wire () in 
      w, [Axiom(w, (sigma, (Term.unusable_var, t)))]
    | Term.ConstW(Term.Cintprint as c) 
    | Term.ConstW(Term.Cintadd as c) | Term.ConstW(Term.Cintsub as c) 
    | Term.ConstW(Term.Cintmul as c) | Term.ConstW(Term.Cintdiv as c) 
    | Term.ConstW(Term.Cinteq as c) | Term.ConstW(Term.Cintslt as c) 
    | Term.ConstW(Term.Cprint _ as c) | Term.ConstW(Term.Cpop(_) as c)
    | Term.ConstW(Term.Cpush _ as c) | Term.ConstW(Term.Ccall _ as c) ->
      let w = fresh_wire () in
      let x = Term.variant_var_avoid "x" sigma in 
      w, [Axiom(w, (sigma, (x, Term.mkApp (Term.mkConstW c) (Term.mkVar x))))]
    | Term.ExternalU _ ->
      failwith "circuit: term not canonized" 
  and compile_in_box (c: Term.var) (sigma: Term.var list) 
        (gamma: wire context) (t: Term.t) =
    let (gamma_in_box, i_enter_box) = enter_box gamma in
    let (w_t, i_t) = compile (c :: sigma) gamma_in_box t in
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
  (*  List.iter (fun e -> match e with
      | (U.Type_eq(a,b,_)) -> Printf.printf "%s = %s\n" 
      (Printing.string_of_type a)
      (Printing.string_of_type b)
      | (U.Basetype_eq(a,b,_)) -> Printf.printf "%s = %s\n" 
      (Printing.string_of_basetype a)
      (Printing.string_of_basetype b)
      ) eqs;
      List.iter (fun (a,b) -> Printf.printf "%s <= %s\n" 
      (Printing.string_of_basetype a)
      (Printing.string_of_basetype b))
      ineqs;
      Printf.printf "======\n";*)
  U.unify_eqs eqs;
  (*    Printf.printf "sol\n";
        List.iter (fun (a,b) -> Printf.printf "%s <= %s\n" 
        (Printing.string_of_basetype a)
        (Printing.string_of_basetype b)) ineqs;
        Printf.printf "======\n";*)

  let cmp a b = Int.compare (Basetype.find a).id (Basetype.find b).id in
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
            (*
            List.iter ~f:(fun a -> Printf.printf "%s,  " (Printing.string_of_basetype a)) xs;
              Printf.printf "%s\n" (Printing.string_of_basetype alpha);
            *)
            let recty = Basetype.Data.fresh_id "conty" in
            let params = List.filter fv_unique 
                           ~f:(fun beta -> not (Basetype.equals beta alpha)) in
            let n = List.length params in
            Basetype.Data.make recty ~nparams:n ~discriminated:false;
            let data = Basetype.newty (Basetype.DataW(recty, params)) in
            let sol = 
              if constraint_recursive then 
                Basetype.newty (Basetype.BoxW(data)) 
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
            (* Printf.printf "Declaring type: %s\n" (Printing.string_of_data recty); *)
            sol 
          end
        else 
          (assert (xs <> []);
           List.hd_exn xs) in
      U.unify_eqs [U.Basetype_eq(sol, alpha, None)]
            (*
       | Basetype.DataW("ref", [beta]) ->
       (  match xs with
       [x1] -> U.unify_pairs [x1 , beta, Some ContextShape]
       | _ -> failwith "todo"
       )
    *)
    | _ -> 
        assert false 
  in
  List.iter joined_lower_bounds ~f:solve_ineq 
    (*
   Printf.printf "sol\n";
   List.iter (fun (a,b) -> Printf.printf "%s = %s\n" 
   (Printing.string_of_type a)
   (Printing.string_of_type b)) ineqs;
   Printf.printf "======\n" *)

exception Not_Leq               

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from alpha to beta.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let embed (a: Basetype.t) (b: Basetype.t) (t: Term.t): Term.t =
  if Basetype.equals a b then 
    t
  else 
    (* TODO *)
    match Basetype.finddesc b with
    (*
       | Basetype.DataW("ref", [b]) ->
       if Basetype.equals a b then
       Term.mkLambdaW(("x", None), Term.mkInW "ref" 0 (Term.mkVar "x"))
       else 
       raise Not_Leq
    *)
    | Basetype.BoxW(c) ->
      begin
        match Basetype.finddesc c with          
        | Basetype.DataW(id, l) ->
          let cs = Basetype.Data.constructor_types id l in
          let rec inject l n =
            match l with 
            | [] -> raise Not_Leq
            | b1 :: bs ->
              if Basetype.equals a b1 then
                Term.mkTerm (
                  Term.BindW((t, a), 
                             ("x", Term.mkBox (Term.mkInW id n (Term.mkVar "x"))))
                )
              else 
                inject bs (n + 1) in
          inject cs 0
        | _ -> raise Not_Leq
      end
    | Basetype.DataW(id, l) ->
      let cs = Basetype.Data.constructor_types id l in
      let rec inject l n =
        match l with 
        | [] -> raise Not_Leq
        | b1 :: bs ->
          if Basetype.equals a b1 then
            Term.mkTerm (
              Term.BindW((t, a), 
                         ("x", (Term.mkInW id n (Term.mkVar "x"))))
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
let project (a: Basetype.t) (b: Basetype.t) (t : Term.t) : Term.t =
  let select id params x =
    let cs = Basetype.Data.constructor_types id params in
    let rec sel cs n =
      match cs with 
      | [] -> 
        raise Not_Leq
      | c1 :: rest ->
        if Basetype.equals a c1 then
          Term.mkTerm (Select(id, params, Term.mkVar x, n))
        else
          sel rest (n + 1) in    
    sel cs 0 in
  if Basetype.equals a b then
    t
  else 
    match Basetype.finddesc b with
    | Basetype.BoxW(c) ->
      begin
        match Basetype.finddesc c with          
        | Basetype.DataW(id, params) ->
          let t1 = select id params "x" in
          let t2 = Term.mkTerm (Term.BindW((Term.mkUnbox (Term.mkVar "y"), c), 
                                           ("x", t1))) in
          let t3 = Term.mkTerm (Term.BindW((t, b), 
                                           ("y", t2))) in
          t3
        | _ -> raise Not_Leq
      end
    | Basetype.DataW(id, params) ->
      let t1 = select id params "x" in
      let t2 = Term.mkTerm (Term.BindW((t, b), 
                                       ("x", t1))) in
      t2
    | _ -> raise Not_Leq

(*
 * Infers types in the string diagram and instantiated the
 * terms in the Der- and Axiom-nodes so that the pre_term 
 * computed below will in fact be a proper term and we 
 * won't have to run type inference on it.
 *
 * Inequality constraints are solved *after* all other equality constraints are
 * solved. This corresponds to first computing the constraints that the rules
 * impose locally and then connecting them with the inequality constraints.
 * TODO: We should prove that this is correct!
*)
let infer_types (c : t) : unit =
  let rec constraints (instructions: instruction list) 
    : type_constraint list  =
    match instructions with
    | [] -> []
    | Axiom(w1, (s, (y, f)))::rest -> 
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let x = "x" in
      (* ensure that x is fresh *)
      let y' = Term.variant_var y in
      let f' = Term.variant f in 
      let s' = List.map ~f:Term.variant_var s in
      (* avoid accidental capture of y *)
      let s'' = List.map 
                  ~f:(fun z -> if z=y' then Term.unusable_var else z) s' in
      (*
      (List.iter ~f:(fun x -> Printf.printf "%s " x) s);
      (Printing.print_term f');
        (Printing.print_term (Term.let_tupleW x (s'', f')));
      *)
      let beta = principal_typeW
                   [(x, sigma); (y', alpha)] []
                   (Term.let_tupleW x (s'', f')) in 
      (*
      (Printing.print_term (Term.let_tupleW x (s'', f')));
      flush stdout;
      Printf.printf "Axiom:  %s (%s, %s)" 
        (Printing.string_of_basetype beta)
        (Printing.string_of_basetype sigma)
        (Printing.string_of_basetype alpha);*)
      beq_constraint w1.type_back (tensor sigma alpha) ::
      beq_constraint w1.type_forward (tensor sigma beta) ::
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
        w3.type_back
        (tensor sigma2 (sum alpha2 beta2)) ::
      (constraints rest)
    | Der(w1, w2, (s, f))::rest ->
      let sigma1 = Basetype.newty Basetype.Var in
      let alpha1 = Basetype.newty Basetype.Var in
      let beta1 = Basetype.newty Basetype.Var in
      beq_constraint
        w2.type_forward (tensor sigma1 beta1) ::
      beq_constraint
        w1.type_back (tensor sigma1 (tensor alpha1 beta1)) ::
      let sigma2 = Basetype.newty Basetype.Var in
      let alpha2 = Basetype.newty Basetype.Var in
      let x = "x" in
      (* ensure "x" is fresh *)
      let f' = Term.variant f in
      let s' = List.map ~f:Term.variant_var s in
      (*
        Printf.printf "Der: %s" (Printing.string_of_termW (let_tupleW x (s', f')));
      *)
      let tyf = principal_typeW [(x, sigma2)] [] (Term.let_tupleW x (s', f')) in 
      beq_constraint
        w1.type_forward (tensor sigma2 (tensor tyf alpha2)) ::
      beq_constraint
        w2.type_back (tensor sigma2 alpha2) ::
      (constraints rest)
    | Case(id, params, w1 (* \Tens{A+B} X *), ws) :: rest ->
      (*let n = Basetype.Data.params id in*)
      let data = Basetype.newty (Basetype.DataW(id, params)) in
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
    | Bind(w1 (* (\Tens A (1 => B))^* *), w2 (* A => B *)) :: rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      let one = Basetype.newty Basetype.OneW in
      beq_constraint 
        w1.type_forward (tensor sigma (tensor alpha one)) :: 
      beq_constraint
        w1.type_back (tensor sigma (tensor alpha beta)) :: 
      beq_constraint
        w2.type_forward (tensor sigma beta) :: 
      beq_constraint
        w2.type_back (tensor sigma alpha) :: 
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
    | Seq(w1 (* (A=>B)^* *), w2 (* (B=>C)^* *), w3 (* A=>C *)) :: rest ->
      let sigma = Basetype.newty Basetype.Var in
      let alpha = Basetype.newty Basetype.Var in
      let beta = Basetype.newty Basetype.Var in
      let delta = Basetype.newty Basetype.Var in
      beq_constraint w1.type_forward (tensor sigma alpha) ::
      beq_constraint w1.type_back (tensor sigma beta) ::
      beq_constraint w2.type_forward (tensor sigma beta) ::
      beq_constraint w2.type_back (tensor sigma delta) ::
      beq_constraint w3.type_forward (tensor sigma delta) ::
      beq_constraint w3.type_back (tensor sigma alpha) ::
      (constraints rest) in
  try
    let cs = constraints c.instructions in
    solve_constraints cs;
  with 
  | U.Not_Unifiable _ -> 
    failwith "Internal error: cannot unify constraints in compilation"

let circuit_of_termU (t : Term.t) : t =
 (* Printing.print_term t;*)
  let c = raw_circuit_of_termU [] [] t in
  let _ = infer_types c in 
  c

let dot_of_circuit 
      ?title:(title = "")
      ?wire_style:(wire_style = fun _ -> "") 
      (c: t) : string = 
  let node_name ins =
    match ins with
    | Axiom(w1, _) -> 
      Printf.sprintf "\"Axiom({%i,%i})\"" w1.src w1.dst
    | Tensor(w1, w2, w3) -> 
      Printf.sprintf "\"Tensor({%i,%i},{%i,%i},{%i,%i})\"" 
        w1.src w1.dst w2.src w2.dst w3.src w3.dst
    | Der(w1, w2, _) -> 
      Printf.sprintf "\"Der({%i,%i},{%i,%i})\"" 
        w1.src w1.dst w2.src w2.dst 
    | Case(id, _, w1, ws) -> 
      Printf.sprintf "\"Case(%s, {%i,%i},%s)\"" 
        id w1.src w1.dst 
        (String.concat ~sep:"," (List.map ~f:(fun w -> Printf.sprintf "{%i,%i}" w.src w.dst) ws))
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
    | Seq(w1, w2, w3) -> 
      Printf.sprintf "\"Seq({%i,%i},{%i,%i},{%i,%i})\"" 
        w1.src w1.dst w2.src w2.dst w3.src w3.dst
  in 
  let node_label ins =
    let ws = wires [ins] in
    let name =
      match ins with
      | Axiom(_, _) -> "axiom(...)"
      | Tensor(_, _, _) -> "&otimes;"
      | Der(_, _, _) -> "&pi;_..."
      | Case(_, _, _, _) -> "case"
      | Door(_, w) -> 
        if w.src = -1 then "\", shape=\"plaintext" else "&uarr;"
      | Assoc(_, _) -> "assoc;"
      | LWeak(_, _) -> "lweak"
      | Bind(_, _) -> "bind"
      | Seq(_, _, _) -> "seq"
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
        List.fold_right (wires [node])
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
        Buffer.add_string buf (Printf.sprintf "[label=\"%i(%s)\"]" w.dst (Printing.string_of_basetype w.type_forward));
        Buffer.add_string buf ";\n ";
      with Not_found -> () (* Weakening *) in
    List.iter instructions_with_result 
      ~f:(fun srcins -> List.iter ~f:(edge srcins) (wires [srcins])) 
  in
  Buffer.add_string buf "digraph G {\n labelloc=t; label=\"";
  Buffer.add_string buf title;
  Buffer.add_string buf "\";fontname=Monospace;fontcolor=blue;fontsize=36;";
  nodes ();
  edges ();
  Buffer.add_string buf "}";
  Buffer.contents buf

