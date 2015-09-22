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
  match Int.Table.find name_table (Type.repr_id t) with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_table ~key:(Type.repr_id t) ~data:name;
    name

let name_base_table = Int.Table.create ()
let name_of_basetypevar t =
  match Int.Table.find name_base_table (Basetype.repr_id t) with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_base_table
      ~key:(Basetype.repr_id t) ~data:name;
    name

let string_of_basetype (ty: Basetype.t): string =
  let open Basetype in
  let cycle_nodes =
    let cycles = Basetype.dfs_cycles ty |> List.map ~f:Basetype.repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Basetype.t) l =
    let rec s l =
      match l with
      | `Summand -> 
        begin
          match case t with
          | Var -> s `Factor
          | Sgn st ->
            begin match st with
            | DataB(id, [t1; t2]) when id = Data.sumid 2 ->
              Printf.sprintf "%s + %s" (str t1 `Summand) (str t2 `Factor)
            | DataB(id, []) when id = Data.sumid 0 -> "void"
            | DataB(id, []) -> id
            | DataB(id, ls) ->
              (*if not (Data.is_discriminated id || Data.is_recursive id) then
                begin
                  let cs = Data.constructor_types id ls in
                  Printf.sprintf "union<%s>"  
                    (List.map cs ~f:(fun t2 -> str t2 `Summand)
                     |> String.concat ~sep:", ")
                end
                else*)
                Printf.sprintf "%s<%s>" id 
                  (List.map ls ~f:(fun t2 -> str t2 `Summand)
                   |> String.concat ~sep:", ")
            | PairB _ | EncodedB _ | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
              s `Factor
            end
        end
      | `Factor ->
        begin
          match case t with
          | Var -> s `Atom
          | Sgn st ->
            begin
              match st with
              | PairB(t1, t2) -> str t1 `Factor ^ " * " ^ str t2 `Atom
              | DataB _ | EncodedB _ | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
                s `Atom
            end
        end
      | `Atom ->
        begin
          match case t with
          | Var -> "\'" ^ (name_of_basetypevar t)
          | Sgn st ->
            begin
              match st with
              | EncodedB b -> "''" ^ (str b `Atom)
              | IntB -> "int"
              | ZeroB -> "void"
              | UnitB -> "unit"
              | BoxB(b) -> Printf.sprintf "box<%s>" (str b `Atom)
              | ArrayB(b) -> Printf.sprintf "array<%s>" (str b `Atom)
              | DataB _
              | PairB _  -> Printf.sprintf "(%s)" (s `Summand)
            end
        end in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetypevar (newvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Summand
        
let string_of_type ?concise:(concise=true) (ty: Type.t): string =
  let open Type in
  let cycle_nodes =
    let cycles = Type.dfs_cycles ty |> List.map ~f:Type.repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Type.t) l =
    let rec s l =
      match l with
      | `Type -> 
        begin
          match case t with
          | Var -> s `Factor
          | Sgn st ->
            match st with
            | FunV(a1, t1) ->
              Printf.sprintf "%s -> %s" (string_of_basetype a1) (str t1 `Type)
            | FunI(a1, t1, t2) ->
              if not concise then
                let cyan = "\027[36m" in
                let default_fg = "\027[39m" in
                Printf.sprintf "%s{%s}%s%s -> %s"
                  cyan (string_of_basetype a1) default_fg (str t1 `Atom) (str t2 `Type)
              else
                Printf.sprintf "%s -> %s" (str t1 `Atom) (str t2 `Type)
            | Base _ | Tensor _ ->
              s `Factor
        end
      | `Factor ->
        begin
          match case t with
          | Var -> s `Atom
          | Sgn st ->
            match st with
            | Tensor(t1, t2) ->
              Printf.sprintf "%s # %s" (str t1 `Factor) (str t2 `Atom)
            | Base _ | FunV _ | FunI _ ->
              s `Atom
        end
      | `Atom ->
        begin
          match case t with
          | Var ->
            "\'\'" ^ (name_of_typevar t)
          | Sgn st ->
            match st with
            | Base(a) ->
              Printf.sprintf "[%s]" (string_of_basetype a)
            | Tensor _ | FunV _ | FunI _ ->
              Printf.sprintf "(%s)" (s `Type)
        end in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "''" ^ (name_of_typevar (newvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Type

let string_of_data id =
  let buf = Buffer.create 80 in
  let name = id in
  let cnames = Basetype.Data.constructor_names id in
  let nparams = Basetype.Data.param_count id in
  let params = List.init nparams ~f:(fun _ -> Basetype.newvar()) in
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
  | Cintprint -> "print"
  | Calloc(_) -> "alloc"
  | Cfree(_) -> "free"
  | Cload(_) -> "load"
  | Cstore(_) -> "store"
  | Carrayalloc _ -> "arrayalloc"
  | Carrayget _ -> "arrayget"
  | Carrayfree _ -> "arrayfree"
  | Cpush a -> "push{" ^ (string_of_basetype a) ^ "}"
  | Cpop a -> "pop{" ^ (string_of_basetype a) ^ "}"
  | Ccall(f, a, b) -> "call(" ^ f ^ ": " ^ (string_of_basetype a) ^
                      " -> " ^ (string_of_basetype b) ^ ") "
  | Cencode a -> "encode{" ^ (string_of_basetype a) ^ "}"
  | Cdecode a -> "decode{" ^ (string_of_basetype a) ^ "}"

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



TEST_MODULE = struct

  TEST "printing of cyclic types 1" =
    let open Basetype in
    let a = newvar () in
    let aa = newty (PairB(a, a)) in
    let b = Type.newvar() in
    let ab = Type.newty (Type.FunV(a, b)) in
    let aab = Type.newty (Type.FunV(a, ab)) in
    let aaab = Type.newty (Type.FunV(aa, ab)) in
    try
      Type.unify_exn aab aaab;
      false
    with
    | Uftype.Cyclic_type ->
      Scanf.sscanf (string_of_type aab)
        "(rec '%s@. '%s * '%s@) -> (rec '%s@. '%s * '%s@) -> ''%s"
        (fun a1 a2 a3 b1 b2 b3 _ -> a1 = a2 && a2 = a3 && b1 = b2 && b2 = b3)
        
  TEST "printing of cyclic types 2" =
    let open Basetype in
    let a = newvar () in
    let b = Type.newvar() in
    let abb = Type.newty (Type.FunI(a, b, b)) in
    try
      Type.unify_exn b abb;
      false
    with
    | Uftype.Cyclic_type ->
      Scanf.sscanf (string_of_type b)
        "(rec ''%s@. ''%s@ -> ''%s@)"
        (fun b1 b2 b3 -> b1 = b2 && b2 = b3)

end
