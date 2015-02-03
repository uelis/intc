%{
(** Parser *)

open Core.Std
open Lexing
open Parsing
open Ast

let illformed msg =
  let s = Parsing.symbol_start_pos () in
  let line = s.pos_lnum in
  let column = s.pos_cnum - s.pos_bol + 1 in
  raise (Decl.Illformed_decl (msg, line, column))

let location_of_pos pos = 
  { Location.line = pos.pos_lnum;
    Location.column = pos.pos_cnum - pos.pos_bol + 1 }

let mkAst d : Ast.t =
  let s = location_of_pos (Parsing.symbol_start_pos ()) in
  let e = location_of_pos (Parsing.symbol_end_pos ()) in
  { Ast.desc = d;
    loc = Some { Location.start_pos = s;
                 Location.end_pos = e } }

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
        match Basetype.case a with
        | Basetype.Var -> ()
        | Basetype.Sgn sa ->
          begin
            match sa with
              EncodedB _ | IntB | UnitB | ZeroB | BoxB _ | ArrayB _ -> ()
            | PairB(a1, a2) ->
              check_rec_occ a1;
              check_rec_occ a2
            | DataB(id', params) ->
              if (id = id') then
                illformed "Recursive occurrences are only allowed within box<...>"
              else
                List.iter params ~f:check_rec_occ
          end
      in
      check_rec_occ cargty;
      (* if all succeeds, add the constructor *)
      Basetype.Data.add_constructor id cname params cargty)
    constructors;
  id

let check_pattern p = 
  let rec vars p =
    match p with
    | PatUnit -> []
    | PatVar(z) -> [z]
    | PatPair(p, q) -> vars p @ vars q in
  let sorted_vars = List.sort ~cmp:Ident.compare (vars p) in
  let rec check sorted_vars =
    match sorted_vars with
    | [] | [_] -> ()
    | x::y::r ->
      if x = y then illformed "Multiple occurrence of variable in pattern."
      else check (y::r) in
  check sorted_vars
  
let type_vars = String.Table.create ()
let type_var (a : string) : Type.t =
  String.Table.find_or_add type_vars a
    ~default:(fun () -> Type.newvar())

let basetype_vars = String.Table.create ()
let basetype_var (a : string) : Basetype.t =
  String.Table.find_or_add basetype_vars a
    ~default:(fun () -> Basetype.newvar())
     
let encoded_vars = String.Table.create ()
let encoded_var (a : string) : Basetype.t =
  String.Table.find_or_add encoded_vars a
    ~default:(fun () -> Basetype.newty (Basetype.EncodedB(Basetype.newvar())))

let clear_type_vars () =
  Hashtbl.clear type_vars;
  Hashtbl.clear basetype_vars

%}

%token LBRACE RBRACE LPAREN RPAREN LANGLE RANGLE LBRACKET RBRACKET
%token PLUS MINUS TIMES DIV
%token COMMA QUOTE DOUBLEQUOTE TRIPLEQUOTE COLON SEMICOLON SHARP EQUALS TO VERTBAR
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
          let def = mkAst (Fn($3, $5)) in
          Decl.TermDecl($2, def) }

identifier:
    | IDENT
        { Ident.global $1 }

identifier_list:
    | identifier
        { [$1] }
    | identifier COMMA identifier_list
        { $1 :: $3 }

term:
    | RETURN term
        { mkAst (Return($2)) }
    | LAMBDA identifier TO term
        { let alpha = Basetype.newvar() in
          let ty = Type.newvar() in
          mkAst (Fun(($2, alpha, ty), $4)) }
    | LAMBDA LPAREN identifier COLON inttype RPAREN TO term
        { let alpha = Basetype.newvar() in
          mkAst (Fun (($3, alpha, $5), $8)) }
    | FN pattern TO term
       { mkAst (Fn($2, $4)) }
    | COPY term AS identifier_list IN term
       { if List.contains_dup $4 then
           illformed "Duplicate variable in copy term.";
         mkAst (Copy($2, ($4, $6))) }
    | LET LPAREN identifier SHARP identifier RPAREN EQUALS term IN term
       { if $3 = $5 then
           illformed "Duplicate variable in pattern.";
         mkAst (LetPair($8, ($3, $5, $10))) }
    | VAL pattern EQUALS term IN term
        { mkAst (Bind($4, ($2, $6))) }
    | IF term THEN term ELSE term
        { mkAst (Case(Basetype.Data.boolid, $2,
                      [(PatUnit, $4); (PatUnit, $6)])) }
    | CASE term OF term_cases
       { let id, c = $4 in
         let indices, cases =
           List.sort c ~cmp:(fun (i, _) (j, _) -> compare i j)
           |> List.unzip in
         (* indices must be [1, ..., length indices] *)
         List.iteri indices ~f:(fun i j ->
           if i <> j then
             illformed "case must match each constructor exactly once!");
         mkAst (Case(id, $2, cases))
       }
    | term_app SEMICOLON term
       { mkAst (Bind($1, (PatUnit, $3))) }
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
           illformed (Printf.sprintf "Undefined constructor %s" $1)
       }

term_case:
    | term_constr TO
       { let id, i = $1 in (id, i, PatVar(Ident.fresh "unused")) }
    | term_constr pattern TO
       { let id, i = $1 in (id, i, $2) }

term_cases:
    | term_case term
    %prec THEN
       { let id, i, p = $1 in
         (id, [(i, (p, $2))]) }
    | term_case term VERTBAR term_cases
        {  let id, i, p = $1 in
           let id', r = $4 in
            if id = id' then (id, (i, (p, $2)) :: r)
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
       { let alpha = Basetype.newvar() in
         mkAst (Const(Calloc(alpha)))}
    | FREE
       { let alpha = Basetype.newvar() in
         mkAst (Const(Cfree(alpha))) }
    | LOAD
       { let alpha = Basetype.newvar() in
         mkAst (Const(Cload(alpha))) }
    | STORE
       { let alpha = Basetype.newvar() in
         mkAst (Const(Cstore(alpha))) }
    | ARRAYALLOC
       { let alpha = Basetype.newvar() in
         mkAst (Const(Carrayalloc(alpha)))}
    | ARRAYFREE
       { let alpha = Basetype.newvar() in
         mkAst (Const(Carrayfree(alpha)))}
    | ARRAYGET
       { let alpha = Basetype.newvar() in
         mkAst (Const(Carrayget(alpha)))}
    | ENCODE
       { let alpha = Basetype.newvar() in
         mkAst (Const(Cencode(alpha))) }
    | DECODE LPAREN basetype COMMA term RPAREN
       { mkAst (App(mkAst (Const(Cdecode($3))), $5)) }
    | PUSH LPAREN basetype COMMA term RPAREN
        { mkAst (App(mkAst (Const(Cpush($3))), $5)) }
    | POP LPAREN basetype RPAREN
        { mkAst (App(mkAst (Const(Cpop($3))), mkAst UnitV)) }
    | CALL LPAREN IDENT COLON basetype TO basetype COMMA term RPAREN
        { mkAst (App(mkAst (Const(Ccall($3, $5, $7))), $9)) }
    | HACK LPAREN term COLON inttype RPAREN
       { mkAst (Direct($5, $3)) }
    | PRINT STRING
        { mkAst (App(mkAst (Const(Cprint $2)), mkAst (UnitV))) }

raw_pattern:
    | identifier
       { PatVar($1) }
    | LPAREN RPAREN
        { PatUnit }
    | LPAREN raw_pattern COMMA raw_pattern RPAREN
        { PatPair($2, $4) }
    | LPAREN raw_pattern RPAREN
        { $2 }

pattern:
    | raw_pattern
        { let p = $1 in
          check_pattern p;
          p }

dataW:
    | TYPE datadeclW EQUALS constructorsW
      { let id, params = $2 in
        let cons = $4 in
          mkDatatype id params cons
       }

datadeclW:
    | IDENT
      { $1, [] }
    | IDENT LANGLE dataparamsW RANGLE
      { let ty = $1 in
        let params = $3 in
          ty, params }

dataparamsW:
    | QUOTE IDENT
      { [basetype_var $2] }
    | QUOTE IDENT COMMA dataparamsW
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
    | QUOTE IDENT
      { basetype_var $2 }
    | TRIPLEQUOTE IDENT
      { encoded_var $2 }
    | UNIT
      { Basetype.newty (Basetype.UnitB) }
    | NAT
      { Basetype.newty (Basetype.IntB) }
    | BOX LANGLE basetype RANGLE
      { Basetype.newty (Basetype.BoxB($3)) }
    | ARRAY LANGLE basetype RANGLE
      { Basetype.newty (Basetype.ArrayB($3)) }
    | IDENT
      { Basetype.newty (Basetype.DataB($1, [])) }
    | IDENT LANGLE basetype_list RANGLE
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
      { Type.newty (Type.FunI(Basetype.newvar(), $1, $3)) }
    | basetype TO inttype
      {  Type.newty (Type.FunV($1, $3)) }

inttype_factor:
    | inttype_atom
      { $1 }
    | inttype_factor SHARP inttype_atom
      { Type.newty (Type.Tensor($1, $3)) }

inttype_atom:
    | DOUBLEQUOTE IDENT
        { type_var $2 }
    | LBRACKET basetype RBRACKET
        { Type.newty (Type.Base $2) }
    | LPAREN inttype RPAREN
      { $2 }
%%
