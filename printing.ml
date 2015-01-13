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
  match Int.Table.find name_table (Type.find t).Type.id with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_table ~key:(Type.find t).Type.id ~data:name;
    name

let name_base_table = Int.Table.create ()
let name_of_basetypevar t =
  match Int.Table.find name_base_table (Basetype.find t).Basetype.id with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_base_table
      ~key:(Basetype.find t).Basetype.id ~data:name;
    name

module BasetypeAlgs = Types.Algs(Basetype)

let string_of_basetype (ty: Basetype.t): string =
  let open Basetype in
  let cycle_nodes =
    let cycles = BasetypeAlgs.dfs_cycles ty in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Basetype.t) l =
    let rec s l =
      match l with
      | `Summand -> 
        begin
          match Basetype.finddesc t with
          | DataB(id, [t1; t2]) when id = Data.sumid 2 ->
            (str t1 `Summand) ^ " + " ^ (str t2 `Factor)
          | DataB(id, []) when id = Data.sumid 0 -> "0"
          | DataB(id, []) -> id
          | DataB(id, ls) ->
            id ^ "<" ^
            (List.map ls ~f:(fun t2 -> str t2 `Summand)
             |> String.concat ~sep:", ") ^
            ">"
          | PairB _ | Var | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
            s `Factor
          | Link _ -> assert false
        end
      | `Factor ->
        begin
          match Basetype.finddesc t with
          | PairB(t1, t2) -> str t1 `Factor ^ " * " ^ str t2 `Atom
          | DataB _ | Var | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
            s `Atom
          | Link _ -> assert false
        end
      | `Atom ->
        begin
          match Basetype.finddesc t with
          | Var -> "\'" ^ (name_of_basetypevar t)
          | IntB -> "int"
          | ZeroB -> "0"
          | UnitB -> "unit"
          | BoxB(b) -> "box<" ^ str b `Atom ^ ">"
          | ArrayB(b) -> "array<" ^ str b `Atom ^ ">"
          | DataB _
          | PairB _  -> "(" ^ s `Summand ^ ")"
          | Link _ -> assert false
        end in
    let tid = (Basetype.find t).id in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetypevar (Basetype.newtyvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Summand
        
module TypeAlgs = Types.Algs(Type)
                    
let string_of_type ?concise:(concise=true) (ty: Type.t): string =
  let open Type in
  let cycle_nodes =
    let cycles = TypeAlgs.dfs_cycles ty in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Type.t) l =
    let rec s l =
      match l with
      | `Type -> 
        begin
          match Type.finddesc t with
          | Type.FunV(a1, t1) ->
            string_of_basetype a1 ^ " -> " ^ str t1 `Type
          | Type.FunI(a1, t1, t2) ->
            if not concise then
              "\027[36m" ^
              "{" ^ (string_of_basetype a1) ^ "}" ^
              "\027[30m" ^
              (str t1 `Atom) ^ " -> " ^ (str t2 `Type)
            else
              (str t1 `Atom) ^ " -> " ^ (str t2 `Type)
          | Type.Var | Type.Base _ | Type.Tensor _ ->
            s `Factor
          | Type.Link _ -> assert false
        end
      | `Factor ->
        begin
          match Type.finddesc t with
          | Type.Tensor(t1, t2) ->
            str t1 `Factor ^ " # " ^ str t2 `Atom
          | Type.Var | Type.Base _ | Type.FunV _ | Type.FunI _ ->
            s `Atom
          | Type.Link _ -> assert false
        end
      | `Atom ->
        begin
          match Type.finddesc t with
          | Type.Var ->
            "\'\'" ^ (name_of_typevar t)
          | Type.Base(a) ->
            "[" ^ (string_of_basetype a) ^ "]"
          | Type.Tensor _ | Type.FunV _ | Type.FunI _ ->
            "(" ^ s `Type ^ ")"
          | Type.Link _ -> assert false
        end in
    let tid = (Type.find t).id in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetypevar (Basetype.newtyvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Type

(* TODO: make tests
   let t1 = Type.newty Type.Var
   let t2 = Type.newty (Type.FunI(Basetype.newtyvar(), t1 ,t1))
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

let string_of_val_const (c: Ast.value_const) : string =
  let open Ast in
  match c with
  | Cundef _ -> "undef"
  | Cintconst i -> Printf.sprintf "%i" i

let string_of_op_const (c: Ast.op_const) : string =
  let open Ast in
  match c with
  | Cprint s -> "print(\"" ^ (String.escaped s) ^ "\")"
  | Cintadd -> "intadd"
  | Cintsub -> "intsub"
  | Cintmul -> "intmul"
  | Cintdiv -> "intdiv"
  | Cinteq -> "inteq"
  | Cintlt -> "intlt"
  | Cintslt -> "intslt"
  | Cintshl -> "intshl"
  | Cintshr -> "intshr"
  | Cintsar -> "intsar"
  | Cintand -> "intand"
  | Cintor  -> "intor"
  | Cintxor -> "intxor"
  | Cintprint -> "intprint"
  | Calloc(_) -> "alloc"
  | Cfree(_) -> "free"
  | Cload(_) -> "load"
  | Cstore(_) -> "store"
  | Carrayalloc _ -> "arrayalloc"
  | Carrayget _ -> "arrayget"
  | Carrayfree _ -> "arrayfree"
  | Cpush(_) -> "push"
  | Cpop(_) -> "pop"
  | Ccall(f, a, b) -> "call(" ^ f ^ ": " ^ (string_of_basetype a) ^
                      " -> " ^ (string_of_basetype b) ^ ") "
  | Cencode(a, b) -> "encode(" ^ (string_of_basetype a) ^
                     ", " ^ (string_of_basetype b) ^ ") "
  | Cdecode(a, b) -> "decode(" ^ (string_of_basetype a) ^
                     ", " ^ (string_of_basetype b) ^ ") "

let fprint_ast (f: Format.formatter) (term: Ast.t): unit =
  let open Ast in
  let open Format in
  let rec s_pattern (p: Ast.pattern): unit =
    match p with
    | PatUnit -> fprintf f "()"
    | PatVar x -> fprintf f "%s" (Ident.to_string x)
    | PatPair(p1, p2) ->
      fprintf f "(";
      s_pattern p1;
      fprintf f ", ";
      s_pattern p2;
      fprintf f ")" in
  let rec s_term (t: Ast.t): unit =
    match t.desc with
    | Return(t) ->
      fprintf f "return @[";
      s_term t;
      fprintf f "@]"
    | Fn(p, t1) ->
      fprintf f "@[<hv 1>fn ";
      s_pattern p;
      fprintf f " ->@;";
      s_term t1;
      fprintf f "@]"
    | Fun((x, _, _), t1) ->
      fprintf f "@[<hv 1>\\%s ->@;" (Ident.to_string x);
      s_term t1;
      fprintf f "@]"
    | Copy(t1, (xs, t2)) ->
      fprintf f "copy @[";
      s_term t1;
      fprintf f "@] as %s in@ @[" (String.concat ~sep:", " (List.map ~f:Ident.to_string xs));
      s_term t2;
      fprintf f "@]"
    | LetPair(t1, (x, y, t2)) ->
      fprintf f "@[<hv 1>let %s # %s =@ " (Ident.to_string x) (Ident.to_string y);
      s_term t1;
      fprintf f "@] in@ @[";
      s_term t2;
      fprintf f "@]"
    | Bind(t1, (p, t2)) ->
      fprintf f "@[<hv 1>val ";
      s_pattern p;
      fprintf f " =@ ";
      s_term t1;
      fprintf f "@] in@ @[";
      s_term t2;
      fprintf f "@]"
    | Case(id, t1, l) ->
      fprintf f "@[<hv>case ";
      s_term t1;
      fprintf f " of ";
      let k = ref 0 in
      List.iter l
        ~f:(fun (p, t) ->
          let conname = List.nth_exn (Basetype.Data.constructor_names id) !k in
          if !k > 0 then fprintf f "@ | " else fprintf f "@   ";
          fprintf f "@[<hv 2>%s(" conname;
          s_pattern p;
          fprintf f ") ->@ ";
          k := !k + 1;
          s_term t;
          fprintf f "@]";
        );
      fprintf f "@]"
    | InV(id, k, t1) ->
      let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
      fprintf f "%s(@[" cname;
      s_term_atom t1;
      fprintf f ")@]"
    | App _ | Var _ | ConstV _ | Const _ | UnitV | FstV _ | SndV _ | SelectV _
    | PairV _ | TypeAnnot _ | Direct _ | Pair _
      -> s_term_app t
  and s_term_app (t: Ast.t) =
    match t.desc with
    | App(t1, t2) ->
      s_term_app t1;
      fprintf f "@ ";
      s_term_atom t2
    | Var _ | ConstV _ | Const _ | UnitV
    | PairV _ | TypeAnnot _
    | InV _ | FstV _ | SndV _ | Return _ | Bind _ | Case _ | SelectV _
    | Fn _ | Fun _ | Copy _ | Pair _ | LetPair _ | Direct _
      -> s_term_atom t
  and s_term_atom (t: Ast.t) =
    match t.desc with
    | Var(x) ->
      fprintf f "%s" (Ident.to_string x)
    | UnitV ->
      fprintf f "()"
    | ConstV(s) ->
      fprintf f "%s" (string_of_val_const s)
    | FstV(t1) ->
      fprintf f "@[fst(";
      s_term t1;
      fprintf f ")@]"
    | SndV(t1) ->
      fprintf f "@[snd(";
      s_term t1;
      fprintf f ")@]"
    | PairV(t1, t2) ->
      fprintf f "(@[";
      s_term t1;
      fprintf f "@],@ @[";
      s_term t2;
      fprintf f "@])";
    | Pair(t1, t2) ->
      fprintf f "(@[";
      s_term t1;
      fprintf f "@] #@ @[";
      s_term t2;
      fprintf f "@])";
    | SelectV(_, _, t1, i) ->
      fprintf f "@[<hv>select(";
      s_term t1;
      fprintf f ", %i)@]" i
    | Const(s) ->
      fprintf f "%s" (string_of_op_const s)
    | Direct(a, t) ->
      fprintf f "@[<hv 2>direct(";
      s_term t;
      fprintf f " : %s@])" (string_of_type a)
    | TypeAnnot(t, _) ->
      s_term_atom t
    | App _ | InV _ | Return _ | Bind _ | Case _
    | Fn _ | Fun _ | Copy _ | LetPair _->
      fprintf f "(@[";
      s_term t;
      fprintf f "@])"
  in
  fprintf f "@[";
  s_term term;
  fprintf f "@]@.\n\n"

let print_ast = fprint_ast Format.std_formatter
let string_of_ast t =
  fprint_ast Format.str_formatter t;
  Format.flush_str_formatter ()
