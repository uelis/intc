%{
  (** Parser
  *)

open Core.Std
open Lexing
open Parsing
open Ast

let illformed msg =
  let s = Parsing.symbol_start_pos () in
  let line = s.pos_lnum in
  let column = s.pos_cnum - s.pos_bol + 1 in
  raise (Decl.Illformed_decl (msg, line, column))

let mkAst_with_pos startp endp d : Ast.t =
  let lp pos = {
    Location.line = pos.pos_lnum;
    Location.column = pos.pos_cnum - pos.pos_bol + 1 } in
  { Ast.desc = d;
    loc = Some{Location.start_pos = lp startp;
               Location.end_pos = lp endp } }

let mkAst d : Ast.t =
  let s = Parsing.symbol_start_pos () in
  let e = Parsing.symbol_end_pos () in
  mkAst_with_pos s e d

let mkDatatype id params constructors =
  let n = List.length params in
  Basetype.Data.make id ~nparams:n ~discriminated:true;
  List.iter
    ~f:(fun (cname, cargty) ->

      (* check for previous definition of constructor *)
      try
        ignore (Basetype.Data.find_constructor cname);
         illformed ("Redefinition of constructor " ^ cname ^ ".")
      with Not_found -> ();

     (* verify that the type variables in the constructor type
      * are contained in the type parameters *)
      let ftv = Basetype.free_vars cargty in
      if List.exists
            ~f:(fun alpha ->
             not (List.exists
                    ~f:(fun beta -> Basetype.equals alpha beta) params))
            ftv then
              illformed ("The free variables in the type of constructor " ^
                 cname ^ " must be contained in the type parameter.");

      (* check that all recursive occurrences of the type are under a box. *)
      let rec check_rec_occ a =
        match Basetype.finddesc a with
        | Var | IntB | UnitB | ZeroB | BoxB _ | ArrayB _ -> ()
        | PairB(a1, a2) ->
          check_rec_occ a1;
          check_rec_occ a2
        | DataB(id', params) ->
          if (id = id') then
            illformed "Recursive occurrences are only allowed within box<...>"
          else
            List.iter params ~f:check_rec_occ
        | Link _ -> assert false
      in
      check_rec_occ cargty;
      (* if all succeeds, add the constructor *)
      Basetype.Data.add_constructor id cname params cargty)
    constructors;
  id

type pattern =
  | PatUnit
  | PatVar of string
  | PatPair of pattern * pattern


let elim_pattern p t =
  (* check pattern *)
  let rec vars p =
    match p with
    | PatUnit -> []
    | PatVar(z) -> [z]
    | PatPair(p, q) -> vars p @ vars q in
  let sorted_vars = List.sort ~cmp:String.compare (vars p) in
  let rec check sorted_vars =
    match sorted_vars with
    | [] | [_] -> ()
    | x::y::r ->
      if x = y then illformed "Multiple occurrence of variable in pattern."
      else check (y::r) in
  check sorted_vars;
  (* eliminate pattern *)
  let rec elim p t =
    match p with
    | PatUnit ->
      let vs = Ast.all_vars t in
      let z = Vargen.mkVarGenerator "u" ~avoid:vs () in
      let unitB = Basetype.newty Basetype.UnitB in
      z,
      mkAst (Bind(mkAst (TypeAnnot(mkAst (Return(mkAst (Var z))),
                                   Type.newty (Type.Base unitB))),
                  (unusable_var, t)))
    | PatVar(z) -> z, t
    | PatPair(p1, p2) ->
      let z1, t1 = elim p1 t in
      let z2, t2 = elim p2 t1 in
      z1, Ast.subst (mkSndV (mkVar z1)) z2
            (Ast.subst (mkFstV (mkVar z1)) z1 t2) in
  elim p t

let type_vars = String.Table.create ()
let type_var (a : string) : Type.t =
   try
     String.Table.find_exn type_vars a
   with Not_found ->
     let alpha = Type.newty Type.Var in
     String.Table.add_exn type_vars ~key:a ~data:alpha;
     alpha

let basetype_vars = String.Table.create ()
let basetype_var (a : string) : Basetype.t =
   try
     String.Table.find_exn basetype_vars a
   with Not_found ->
     let alpha = Basetype.newty Basetype.Var in
     String.Table.add_exn basetype_vars ~key:a ~data:alpha;
     alpha

let clear_type_vars () = Hashtbl.clear type_vars

%}

%token LBRACE RBRACE LPAREN RPAREN LANGLE RANGLE LBRACKET RBRACKET
%token PLUS MINUS TIMES DIV
%token COMMA QUOTE DOUBLEQUOTE COLON SEMICOLON SHARP EQUALS TO VERTBAR
%token FN LAMBDA TYPE UNIT PUSH POP BOX ARRAY ALLOC FREE LOAD STORE CALL NAT
%token ENCODE DECODE
%token INTADD INTSUB INTMUL INTDIV INTEQ INTLT INTSLT
%token INTSHL INTSHR INTSAR INTAND INTOR INTXOR
%token ARRAYALLOC ARRAYFREE ARRAYGET
%token IF THEN ELSE PRINT HACK LET VAL AS OF IN RETURN
%token COPY CASE
%token <int> NUM
%token <string> IDENT
%token <string> CONSTR
%token <string> STRING
%token EOF

%right SEMICOLON
%left EQUALS
%left PLUS MINUS
%left TIMES DIV
%nonassoc THEN
%nonassoc VERTBAR

%start decls
%type <Decl.t list> decls
%type <Ast.t> term
%type <Basetype.t> basetype
%type <Type.t> inttype

%%

decls:
    | EOF
      { [] }
    | decl decls
      { $1 :: $2 }
    | dataW decls
      { $2 }

decl:
    | LET pattern EQUALS term
        { clear_type_vars ();
          match $2 with
          | PatVar(x) -> Decl.TermDecl(x, $4)
          | _ -> illformed "Variable declaration expected."
        }
    | LET pattern COLON inttype EQUALS term
        { clear_type_vars ();
          match $2 with
          | PatVar(x) -> Decl.TermDecl(x, mkAst (TypeAnnot($6, $4)))
          | _ -> illformed "Variable declaration expected."
        }
    | FN identifier pattern EQUALS term
        { clear_type_vars ();
          let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern $3 $5 in
          let def = mkAst (Fn((x, alpha), t)) in
          Decl.TermDecl($2, def) }

identifier:
    | IDENT
        { $1 }

identifier_list:
    | IDENT
        { [$1] }
    | IDENT COMMA identifier_list
        { $1 :: $3 }

term:
    | RETURN term
        { mkAst (Return($2)) }
    | LAMBDA identifier TO term
        { let alpha = Basetype.newty Basetype.Var in
          let ty = Type.newty Type.Var in
          mkAst (Fun(($2, alpha, ty), $4)) }
    | LAMBDA LPAREN identifier COLON inttype RPAREN TO term
        { let alpha = Basetype.newty Basetype.Var in
          mkAst (Fun (($3, alpha, $5), $8)) }
    | FN pattern TO term
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern $2 $4 in
          mkAst (Fn((x, alpha), t)) }
    | COPY term AS identifier_list IN term
       { mkAst (Copy($2, ($4, $6))) }
    | LET LPAREN identifier SHARP identifier RPAREN EQUALS term IN term
        { mkAst (LetPair($8, ($3, $5, $10))) }
    | VAL pattern EQUALS term IN term
        { let x, t = elim_pattern $2 $6 in
          mkAst (Bind($4, (x, t))) }
    | IF term THEN term ELSE term
        { mkAst (Case(Basetype.Data.boolid, $2,
                        [(unusable_var, $4); (unusable_var, $6)])) }
    | CASE term OF term_cases
        {let id, c = $4 in
         let sorted_c = List.sort c
                          ~cmp:(fun (i, _, _) (j, _, _) -> compare i j) in
         let indices = List.map ~f:(fun (i, _, _) -> i) sorted_c in
         let cases = List.map ~f:(fun (_, x, t) -> (x, t)) sorted_c in
         let n = List.length (Basetype.Data.constructor_names id) in
         (* Check that there is a case for all constructors *)
         if (indices = List.init n ~f:(fun i -> i)) then
           mkAst (Case(id, $2, cases))
         else
           illformed "case must match each constructor exactly once!"
       }
    | term_app SEMICOLON term
        { let x, t = elim_pattern PatUnit $3 in
          mkAst (Bind($1, (x, t))) }
    | term_app
       { $1 }
    | term_constr
       { let id, i = $1 in mkAst (InV(id, i,  mkAst (UnitV))) }
    | term_constr term_atom
       { let id, i = $1 in mkAst (InV(id, i, $2)) }

term_constr:
    | CONSTR
       { try Basetype.Data.find_constructor $1
           with Not_found ->
             (* TODO: message *)
             illformed (Printf.sprintf "Undefined constructor %s" $1)
       }

term_case:
  | term_constr TO
       { let id, i = $1 in (id, i, PatVar(unusable_var)) }
    | term_constr pattern TO
        {
          let id, i = $1 in
          (id, i, $2) }

term_cases:
    | term_case term
    %prec THEN
       { let id, i, p = $1 in
         let x, t = elim_pattern p $2 in
         (id, [i,x,t]) }
    | term_case term VERTBAR term_cases
        {  let id, i, p = $1 in
           let x, t = elim_pattern p $2 in
           let id', r = $4 in
            if id = id' then (id, (i, x, t)::r)
            else illformed "Constructors from different types used in case." }

term_app:
    | term_atom
       { $1 }
    | term_app term_atom
       { mkAst (App($1, $2))  }

term_atom:
    | identifier
       { mkAst (Ast.Var($1)) }
    | LPAREN RPAREN
       { mkAst UnitV }
    | LPAREN term RPAREN
       { $2 }
    | LBRACE term RBRACE
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern PatUnit $2 in
          mkAst (Fn((x, alpha), t)) }
    | LPAREN term COMMA term RPAREN
       { mkAst (PairV($2, $4)) }
    | LPAREN term SHARP term RPAREN
       { mkAst (Pair($2, $4)) }
    | NUM
       { mkAst (ConstV(Cintconst($1))) }
    | MINUS NUM
       { mkAst (ConstV(Cintconst(-$2))) }
    | PRINT term_atom
       { mkAst (App(mkAst (Const(Cintprint)), $2)) }
    | INTADD
       { mkAst (Const(Cintadd))}
    | INTSUB
       { mkAst (Const(Cintsub))}
    | INTMUL
       { mkAst (Const(Cintmul))}
    | INTDIV
       { mkAst (Const(Cintdiv))}
    | INTEQ
       { mkAst (Const(Cinteq))}
    | INTLT
       { mkAst (Const(Cintlt))}
    | INTSLT
       { mkAst (Const(Cintslt))}
    | INTSHL
       { mkAst (Const(Cintshl))}
    | INTSHR
       { mkAst (Const(Cintshr))}
    | INTSAR
       { mkAst (Const(Cintsar))}
    | INTAND
       { mkAst (Const(Cintand))}
    | INTOR
       { mkAst (Const(Cintor))}
    | INTXOR
       { mkAst (Const(Cintxor))}
    | ALLOC
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Calloc(alpha)))}
    | FREE
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Cfree(alpha))) }
    | LOAD
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Cload(alpha))) }
    | STORE
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Cstore(alpha))) }
    | ARRAYALLOC
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Carrayalloc(alpha)))}
    | ARRAYFREE
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Carrayfree(alpha)))}
    | ARRAYGET
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (Const(Carrayget(alpha)))}
    | ENCODE
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
          mkAst (Const(Cencode(alpha, beta))) }
    | DECODE LPAREN basetype COMMA term RPAREN
       { let alpha = Basetype.newty Basetype.Var in
         mkAst (App(mkAst (Const(Cdecode(alpha, $3))), $5)) }
    | PUSH LPAREN basetype COMMA term RPAREN
        { mkAst (App(mkAst (Const(Cpush($3))), $5)) }
    | POP LPAREN basetype RPAREN
        { mkAst (App(mkAst (Const(Cpop($3))), mkAst UnitV)) }
    | CALL LPAREN identifier COLON basetype TO basetype COMMA term RPAREN
        { mkAst (App(mkAst (Const(Ccall($3, $5, $7))), $9)) }
    | HACK LPAREN term COLON inttype RPAREN
       { mkAst (Direct($5, $3)) }
    | PRINT STRING
        { mkAst (App(mkAst (Const(Cprint $2)), mkAst (UnitV))) }

pattern:
    | identifier
       { PatVar($1) }
    | LPAREN RPAREN
        { PatUnit }
    | LPAREN pattern COMMA pattern RPAREN
        { PatPair($2, $4) }
    | LPAREN pattern RPAREN
        { $2 }


dataW:
    | TYPE datadeclW EQUALS constructorsW
      { let id, params = $2 in
        let cons = $4 in
          mkDatatype id params cons
       }

datadeclW:
    | identifier
      { $1, [] }
    | identifier LANGLE dataparamsW RANGLE
      { let ty = $1 in
        let params = $3 in
          ty, params }

dataparamsW:
    | QUOTE identifier
      { [basetype_var $2] }
    | QUOTE identifier COMMA dataparamsW
      { let var = basetype_var $2 in
        let vars = $4 in
          if List.exists ~f:(fun alpha -> Basetype.equals var alpha) vars then
             illformed "Type variable appears twice in parameter list."
          else
             var::vars }

constructorsW:
    | CONSTR OF basetype
      { [$1, $3] }
    | CONSTR OF basetype VERTBAR constructorsW
      { ($1, $3) :: $5 }

basetype:
    | basetype_summand
      { $1 }

basetype_summand:
    | basetype_factor
      { $1 }
    | basetype_summand PLUS basetype_factor
      { Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [$1; $3])) }

basetype_factor:
    | basetype_atom
      { $1 }
    | basetype_factor TIMES basetype_atom
      { Basetype.newty (Basetype.PairB($1, $3)) }

basetype_atom:
    | QUOTE identifier
      { basetype_var $2 }
    | UNIT
      { Basetype.newty (Basetype.UnitB) }
    | NAT
      { Basetype.newty (Basetype.IntB) }
    | BOX LANGLE basetype RANGLE
      { Basetype.newty (Basetype.BoxB($3)) }
    | ARRAY LANGLE basetype RANGLE
      { Basetype.newty (Basetype.ArrayB($3)) }
    | identifier
      { Basetype.newty (Basetype.DataB($1, [])) }
    | identifier LANGLE basetype_list RANGLE
      { Basetype.newty (Basetype.DataB($1, $3)) }
    | LPAREN basetype RPAREN
      { $2 }

basetype_list:
    | basetype
      { [$1] }
    | basetype COMMA basetype_list
      { $1 :: $3 }

inttype:
    | inttype_factor
      { $1 }
    | LBRACE basetype RBRACE inttype_atom TO inttype
      { Type.newty (Type.FunI($2, $4, $6)) }
    | inttype_factor TO inttype
      { Type.newty (Type.FunI(Basetype.newty Basetype.Var, $1, $3)) }
    | basetype TO inttype
      {  Type.newty (Type.FunV($1, $3)) }

inttype_factor:
    | inttype_atom
      { $1 }
    | inttype_factor SHARP inttype_atom
      { Type.newty (Type.Tensor($1, $3)) }

inttype_atom:
    | DOUBLEQUOTE identifier
        { type_var $2 }
    | LBRACKET basetype RBRACKET
        { Type.newty (Type.Base $2) }
    | LPAREN inttype RPAREN
      { $2 }
%%
