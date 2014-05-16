open Core.Std
(** Printing of terms and types *)

let name_counter = ref 0

let new_name () =
  let i = !name_counter in
  incr(name_counter);
  let c = Char.of_int_exn (Char.to_int 'a' + i mod 26) in
  let n = i / 26 in
  if (n = 0) then 
    Printf.sprintf "%c" c
  else
    Printf.sprintf "%c%i" c n;;

let reset_names () = 
  name_counter := 0

let name_table = Int.Table.create ()
let name_of_typevar t = 
  match Int.Table.find name_table (Type.find t).id with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_table ~key:(Type.find t).id ~data:name;
    name

let name_base_table = Int.Table.create ()
let name_of_basetypevar t = 
  match Int.Table.find name_base_table (Basetype.find t).id with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_base_table ~key:(Basetype.find t).id ~data:name;
    name

module BasetypeAlgs = Types.Algs(Basetype)

(* 
TODO: unexpected result
# fun (f:'a*('a*'a) -> 'a) -> fn x { f(x,x) }
: |(rec 'a. 'a * 'a) * 'a -> (rec 'b. 'b)| -> (rec 'c. 'c) -> (rec 'd. 'd)
*)
let string_of_basetype (ty: Basetype.t): string =  
  let buf = Buffer.create 80 in
  (* recognize loops and avoid printing infinite types
   * TODO: this is awkward and not properly tested!
  *)
  let cycle_names = 
    let cycles = BasetypeAlgs.dfs_cycles ty in
    let tbl = Int.Table.create () in
    List.iter cycles
      ~f:(fun tid -> Int.Table.replace tbl ~key:tid ~data:None);
    tbl in
  let open Basetype in
  let check_rec t = 
    let tid = (Basetype.find t).id in
    try
      match Int.Table.find_exn cycle_names tid with
      | Some s -> "", Some(s), ""
      | None ->
        let alpha = Basetype.newty Basetype.Var in
        let s = "'" ^ (name_of_basetypevar alpha) in
        Int.Table.replace cycle_names ~key:tid ~data:(Some s);
        "(rec " ^ s ^ ". ", None, ")"
    with Not_found -> "", None, "" in
  (* Printing functions *)
  let rec s_basetype (t: Basetype.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> s_summand t
    end;    
    Buffer.add_string buf after
  and s_summand (t: Basetype.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> 
        begin
          match Basetype.finddesc t with
          | DataW(id, [t1; t2]) when id = Data.sumid 2 ->
            s_summand t1; 
            Buffer.add_string buf " + ";
            s_factor t2 
          | DataW(id, []) when id = Data.sumid 0 ->
            Buffer.add_char buf '0'
          | DataW(id, [])  ->
            Buffer.add_string buf id
          | DataW(id, t1 :: l) ->
            Buffer.add_string buf id;
            Buffer.add_char buf '<';
            s_summand t1;
            List.iter l
              ~f:(fun t2 -> 
                Buffer.add_string buf ", ";
                s_summand t2);
            Buffer.add_string buf ">"
          | TensorW _ | Var | NatW | ZeroW | OneW | BoxW _ ->
            s_factor t
          | Link _ -> assert false
        end
    end;
    Buffer.add_string buf after;
  and s_factor (t: Basetype.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> begin
          match Basetype.finddesc t with
          | TensorW(t1, t2) ->
            s_factor t1;
            Buffer.add_string buf " * ";
            s_atom t2
          | DataW _ | Var | NatW | ZeroW | OneW | BoxW _ ->
            s_atom t
          | Link _ -> assert false
        end
    end;    
    Buffer.add_string buf after
  and s_atom (t: Basetype.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> 
        begin
          match Basetype.finddesc t with
          | Var ->  
            Buffer.add_char buf '\'';
            Buffer.add_string buf (name_of_basetypevar t)
          | NatW -> Buffer.add_string buf "int"
          | ZeroW -> Buffer.add_char buf '0'
          | OneW -> Buffer.add_string buf "unit"
          | BoxW(b) -> 
            Buffer.add_char buf '~';
            s_atom b;
          | DataW _ | TensorW _  ->
            Buffer.add_char buf '(';
            s_basetype t;
            Buffer.add_char buf ')';
          | Link _ -> assert false
        end
    end;    
    Buffer.add_string buf after
  in 
  s_basetype ty;
  Buffer.contents buf

module TypeAlgs = Types.Algs(Type)

let string_of_type ?concise:(concise=true) (ty: Type.t): string =  
  let buf = Buffer.create 80 in
  (* TODO: this is awkward *)
  let cycle_names = 
    let cycles = TypeAlgs.dfs_cycles ty in
    let tbl = Int.Table.create () in
    List.iter cycles ~f:(fun tid -> Int.Table.replace tbl ~key:tid ~data:None);
    tbl in
  let check_rec t = 
    let tid = (Type.find t).id in
    try
      match Int.Table.find_exn cycle_names tid with
      | Some s -> "", Some(s), ""
      | None ->
        let alpha = Type.newty Type.Var in
        let s = "'" ^ (name_of_typevar alpha) in
        Int.Table.replace cycle_names ~key:tid ~data:(Some s);
        "(rec " ^ s ^ ". ", None, ")"
    with Not_found -> "", None, "" in
  (* Printing functions *)
  let rec s_type (t: Type.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> 
        begin
          match Type.finddesc t with
          | Type.FunU(a1, t1, t2) ->
            (* TODO: put colours away *)
            if not concise then
              begin
                Buffer.add_string buf "\027[36m";
                Buffer.add_char buf '{';
                Buffer.add_string buf (string_of_basetype a1);
                Buffer.add_char buf '}';
                Buffer.add_string buf "\027[30m"
              end;
            Buffer.add_string buf "|";
            s_type t1;
            Buffer.add_string buf "| -> ";
            s_type t2
          | Type.FunW _ | Type.Var -> 
            s_atom t
          | Type.Link _ -> assert false        
        end
    end;    
    Buffer.add_string buf after
  and s_atom (t: Type.t) =
    let before, body, after = check_rec t in
    Buffer.add_string buf before;
    begin
      match body with
      | Some body -> Buffer.add_string buf body
      | None -> 
        begin
          match Type.finddesc t with
          | Type.FunW(b1, b2) ->
            Buffer.add_string buf (string_of_basetype b1);
            Buffer.add_string buf " -> ";
            Buffer.add_string buf (string_of_basetype b2)
          | Type.Var -> 
            Buffer.add_string buf "\'\'";
            Buffer.add_string buf (name_of_typevar t)
          | Type.FunU _ ->
            Buffer.add_char buf '(';
            s_type t;
            Buffer.add_char buf ')'
          | Type.Link _ -> assert false
        end
    end;    
    Buffer.add_string buf after in
  s_type ty;
  Buffer.contents buf

(* TODO: make tests
   let t1 = Type.newty Type.Var 
   let t2 = Type.newty (Type.FunU(Basetype.newtyvar(), t1 ,t1))
   module U = Unify.Unify(struct type t = () end)
   let _ = U.unify_eqs [U.Type_eq(t1, t2, None)]
   let _ = Printf.printf "%s\n" (string_of_type t2)
*)
let string_of_data id =
  let buf = Buffer.create 80 in
  let name = id in
  let cnames = Basetype.Data.constructor_names id in
  let nparams = Basetype.Data.params id in
  let params = List.init nparams ~f:(fun _ -> Basetype.newty Basetype.Var) in
  let ctypes = Basetype.Data.constructor_types id params in
  let cs = List.zip_exn cnames ctypes in
  Buffer.add_string buf "type ";
  Buffer.add_string buf name;
  if (nparams > 0) then begin
    Buffer.add_string buf "<";
    Buffer.add_string buf (String.concat ~sep:"," 
                             (List.map ~f:string_of_basetype params));
    Buffer.add_string buf ">";
  end;
  Buffer.add_string buf " = ";
  Buffer.add_string buf 
    (String.concat ~sep:" | " 
       (List.map ~f:(fun (n, t) -> 
          Printf.sprintf "%s of %s" n (string_of_basetype t)) cs));
  Buffer.contents buf

let string_of_val_const (c: Term.value_const) : string =
  let open Term in
  match c with
  | Cundef _ -> "undef"
  | Cintconst i -> Printf.sprintf "%i" i

let string_of_op_const (c: Term.op_const) : string =
  let open Term in
  match c with
  | Cprint s -> "print(\"" ^ (String.escaped s) ^ "\")"
  | Cintadd -> "intadd"
  | Cintsub -> "intsub"
  | Cintmul -> "intmul"
  | Cintdiv -> "intdiv"
  | Cinteq -> "inteq"
  | Cintslt -> "intslt"
  | Cintprint -> "intprint"
  | Cpush(_) -> "push"
  | Cpop(_) -> "pop"
  | Ccall(f, a, b) -> "call(" ^ f ^ ": " ^ (string_of_basetype a) ^ 
                      " -> " ^ (string_of_basetype b) ^ ") "

let fprint_term (f: Format.formatter) (term: Term.t): unit =
  let open Term in
  let open Format in
  let rec s_termW (t: Term.t): unit =
    match t.desc with
    | LambdaW((x, a), t1) ->
      fprintf f "@[<hv 2>fn (%s: %s) {@;" x (string_of_basetype a);
      s_termW t1;
      fprintf f "}@]"
    | LambdaU((x, _, ty), t1) ->
      fprintf f "@[<hv 2>fun (%s: %s) ->@;" x (string_of_type ty);
      s_termW t1;
      fprintf f "@]"
    | HackU(a, t) ->
      fprintf f "@[<hv 2>hack@ ";
      s_termW t;
      fprintf f "@ as %s@]" (string_of_type a)
    | ExternalU((e, a), _) ->
      fprintf f "@[<hv 2>external(%s: %s)@]" e (string_of_type a)
    | CopyU(t1, (x, y, t2)) ->
      fprintf f "copy @[ ";
      s_termW t1;
      fprintf f "@] as %s,%s in@ @[" x y;
      s_termW t2;
      fprintf f "@]"
    | FstW(t1, _, _) ->
      fprintf f "@[fst(";
      s_termW t1;
      fprintf f ")@]"
    | SndW(t1, _, _) ->
      fprintf f "@[snd(";
      s_termW t1;
      fprintf f ")@]"
    | BindW((t1, _), (x, t2)) ->
      fprintf f "@[<hv 2>let %s =@ " x;
      s_termW t1;
      fprintf f "@] in@ @[";
      s_termW t2;
      fprintf f "@]"
    | Select(_, _, t1, i) ->
      fprintf f "@[<hv>select(";
      s_termW t1;
      fprintf f ", %i)@]" i
    | Case(id, _, t1, l) ->
      fprintf f "@[<hv>case ";
      s_termW t1;
      fprintf f " of ";
      let k = ref 0 in 
      List.iter l
        ~f:(fun (x, t) -> 
        let conname = List.nth_exn (Basetype.Data.constructor_names id) !k in
        if !k > 0 then fprintf f "@ | " else fprintf f "@   "; 
        fprintf f "@[<hv 2>%s(%s) ->@ " conname x;
        k := !k + 1;
        s_termW t;
        fprintf f "@]";
      );
      fprintf f "@]"
    | InW((id, k, t1), _) ->
      let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
      fprintf f "%s(@[" cname;
      s_termW_atom t1;
      fprintf f ")@]"
    | App _ | Var _ | ValW _ | ConstW _ | UnitW 
    | PairW _ | Box _ | Unbox _ | TypeAnnot _
      -> s_termW_app t
  and s_termW_app (t: Term.t) =
    match t.desc with
    | App(t1, _, t2) -> 
      s_termW_app t1;
      fprintf f "@ ";
      s_termW_atom t2
    | Var _ | ValW _ | ConstW _ | UnitW 
    | PairW _ | Box _ | Unbox _ | TypeAnnot _ 
    | InW _ | FstW _ | SndW _ | BindW _ | Case _ | Select _
    | LambdaW _ | LambdaU _ | CopyU _ | HackU _ | ExternalU _
      -> s_termW_atom t
  and s_termW_atom (t: Term.t) =
    match t.desc with
    | Var(x) -> 
      fprintf f "%s" x
    | UnitW -> 
      fprintf f "()"
    | ValW(s) -> 
      fprintf f "%s" (string_of_val_const s)
    | ConstW(s) -> 
      fprintf f "%s" (string_of_op_const s)
    | PairW((t1, _), (t2, _)) -> 
      fprintf f "(@[";
      s_termW t1;
      fprintf f "@], @[";
      s_termW t2;
      fprintf f "@])";
    | Box(t1, _) -> 
      fprintf f "~";
      s_termW t1
    | Unbox(t1, _) -> 
      fprintf f "^";
      s_termW t1
    | TypeAnnot(t, _) ->
      s_termW_atom t
    | App _ | InW _ | FstW _ | SndW _ | BindW _ | Case _ | Select _
    | LambdaW _ | LambdaU _ | CopyU _ | HackU _ | ExternalU _->
      fprintf f "(@[";
      s_termW t;
      fprintf f "@])"
  in 
  fprintf f "@[";
  s_termW term; 
  fprintf f "@]@.\n\n"

let print_term = fprint_term Format.std_formatter
let string_of_term t = 
  fprint_term Format.str_formatter t;
  Format.flush_str_formatter ()