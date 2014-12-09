open Core.Std
open Ssa

let fresh_var = Vargen.mkVarGenerator "z" ~avoid:[]

let block_table (func: Ssa.t) =
  let blocks = Int.Table.create () in
  List.iter func.blocks
    ~f:(fun b ->
      let i = (Ssa.label_of_block b).name in
      Int.Table.replace blocks ~key:i ~data:b
    );
  blocks

(**
   Tracing
*)
let trace_block blocks i0 =
  let block = Int.Table.find_exn blocks i0 in
  let l0 = label_of_block block in
  let x0 = fresh_var () in

  (* substitution *)
  let rho = String.Table.create () in
  (* current body *)
  let lets = ref [] in
  (* already visited labels *)
  let visited = Int.Table.create () in

  let rec remove_last_push ls =
    match ls with
    | [] -> None
    | Let(_, Const(Term.Cpush(_), v)) :: rest-> Some (v, rest)
    | l :: rest ->
      begin
        match remove_last_push rest with
        | Some (v, ls') -> Some (v, l::ls')
        | None  -> None
      end in
  let trace_let l =
    match l with
    | Let((x, a), t) ->
      let t' = subst_term (String.Table.find_exn rho) t in
      begin
        match t', !lets with
        | Val v', _ ->
          String.Table.replace rho ~key:x ~data:v'
        | Const(Term.Cpop(_), _), _ ->
          begin
            match remove_last_push !lets with
            | Some (v', lets') ->
              lets := lets';
              String.Table.replace rho ~key:x ~data:v'
            | None ->
              let x' = fresh_var () in
              String.Table.replace rho ~key:x ~data:(Var x');
              lets := Let((x', a), t') :: !lets
          end
        (* quick hack to eliminate Alloc,Store,Load,Free sequences
           immediately *)
          (* TODO:
        | Load(addr1, _), Let((z1, a1), Store(addr2, v, _)) :: rest
          when addr1 = addr2 ->
          String.Table.replace rho ~key:x ~data:v;
          lets := rest @ [Let((z1, a1), Val(Unit))]
        | Free(addr1, _), Let((addr2, anat) , Alloc(_)) :: rest
          when addr1 = Var addr2 ->
          String.Table.replace rho ~key:x ~data:Unit;
          lets := rest @ [Let((addr2, anat), Val(IntConst(0)))]
          *)
        | _ ->
          let x' = fresh_var () in
          String.Table.replace rho ~key:x ~data:(Var x');
          lets := Let((x', a), t') :: !lets
      end in
  let trace_lets lets = List.iter (List.rev lets) ~f:trace_let in
  let flush_lets () =
    let ls = !lets in
    lets := [];
    ls in

  (* tracing of blocks*)
  let rec trace_block i v =
    let block = Int.Table.find_exn blocks i in
    match Int.Table.find visited i with
    | Some i when i > !Opts.opt_trace_loop_threshold ->
      let lets = flush_lets () in
      let dst = label_of_block block in
      Direct(l0, x0, lets, v, dst)
    | _ ->
      begin
        Int.Table.change visited i (function None -> Some 1
                                           | Some i -> Some (i+1));
        (* Printf.printf "%s\n" (string_of_letbndgs !lets); *)
        match block with
        | Unreachable(_) -> Unreachable(l0)
        | Direct(_, x, lets, vr, dst) ->
          String.Table.replace rho ~key:x ~data:v;
          trace_lets lets;
          let vr' = subst_value (String.Table.find_exn rho) vr in
          trace_block dst.name vr'
        | Branch(_, x, lets, (id, params, vc, cases)) ->
          String.Table.replace rho ~key:x ~data:v;
          trace_lets lets;
          let vc' = subst_value (String.Table.find_exn rho) vc in
          begin
            match vc' with
            | In((_, i, vi), _) ->
              let (y, vd, dst) = List.nth_exn cases i in
              String.Table.replace rho ~key:y ~data:vi;
              let vd' = subst_value (String.Table.find_exn rho) vd in
              trace_block dst.name vd'
            | _ ->
              let lets = flush_lets () in
              let cases' =
                List.map cases
                  ~f:(fun (y, vd, dst) ->
                    let y' = fresh_var () in
                    String.Table.replace rho ~key:y ~data:(Var y');
                    let vd' = subst_value (String.Table.find_exn rho) vd in
                    (y', vd', dst)) in
              Branch(l0, x0, lets, (id, params, vc', cases'))
          end
        | Return(_, x, lets, vr, a) ->
          String.Table.replace rho ~key:x ~data:v;
          trace_lets lets;
          let vr' = subst_value (String.Table.find_exn rho) vr in
          let lets = flush_lets () in
          Return(l0, x0, lets, vr', a)
      end in
  let v0 = Var x0 in
  String.Table.replace rho ~key:x0 ~data:v0;
  trace_block i0 v0

let trace (func : Ssa.t) =
  let blocks = block_table func in
  let traced = Int.Table.create () in
  let rev_blocks = ref [] in
  let rec trace_blocks i =
    if not (Int.Table.mem traced i) then
      begin
        Int.Table.replace traced ~key:i ~data:();

        let b = trace_block blocks i in
        rev_blocks := b :: !rev_blocks;
        List.iter (targets_of_block b)
          ~f:(fun l -> trace_blocks l.name)
      end in
  trace_blocks (func.entry_label.name);
  Ssa.make
    ~func_name: func.func_name
    ~entry_label: func.entry_label
    ~blocks: (List.rev !rev_blocks)
    ~return_type: func.return_type

(**
   Shortcutting jumps
*)
let shortcut_block blocks i0 =
  let block = Int.Table.find_exn blocks i0 in

  let shortcut_value (i : label) v =
    let visited = Int.Table.create () in
    let rec shortcut_value (i : label) v =
      if Int.Table.mem visited i.name then
        i, v
      else
        begin
          Int.Table.add_exn visited ~key:i.name ~data:();
          let block = Int.Table.find_exn blocks i.name in
          match block with
          | Direct(_, x, [], vr, dst) ->
            let vr' = subst_value (fun y -> if x = y then v else Var y) vr in
            shortcut_value dst vr'
          | Branch(_, x, [], (_, _, vc, cases)) ->
            let vc' = subst_value (fun y -> if x = y then v else Var y) vc in
            begin
              match vc' with
              | In((_, i, vi), _) ->
                let (y, vd, dst) = List.nth_exn cases i in
                let vd' = subst_value (fun z -> if y = z then vi else Var z)
                            (subst_value (fun z -> if x = z then v else Var z ) vd) in
                shortcut_value dst vd'
              | _ ->
                i, v
            end
          | Unreachable _
          | Direct _
          | Branch _
          | Return _ ->
            i, v
        end in
    shortcut_value i v in

  match block with
  | Direct(l, x, lets, vr, dst) ->
    let dst', vr' = shortcut_value dst vr in
    Direct(l, x, lets, vr', dst')
  | Branch(l, x, lets, (id, params, vc, cases)) ->
    let cases' = List.map cases
                   ~f:(fun (y, vd, dst) ->
                     let dst', vd' = shortcut_value dst vd in
                     (y, vd', dst')) in
    Branch(l, x, lets, (id, params, vc, cases'))
  | Unreachable _
  | Return _ -> block

let shortcut_jumps (func : Ssa.t) =
  let blocks = block_table func in
  let traced = Int.Table.create () in
  let rev_blocks = ref [] in
  let rec shortcut_blocks i =
    if not (Int.Table.mem traced i) then
      begin
        Int.Table.replace traced ~key:i ~data:();

        let b = shortcut_block blocks i in
        rev_blocks := b :: !rev_blocks;
        List.iter (targets_of_block b)
          ~f:(fun l -> shortcut_blocks l.name)
      end in
  shortcut_blocks (func.entry_label.name);
  Ssa.make
    ~func_name: func.func_name
    ~entry_label: func.entry_label
    ~blocks: (List.rev !rev_blocks)
    ~return_type: func.return_type
