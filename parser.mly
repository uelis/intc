%{
(************************************************************************
*
*  parser.mly
*
************************************************************************)

open Core.Std
open Lexing
open Parsing
open Term
open Decls

let illformed msg =
  let s = Parsing.symbol_start_pos () in 
  let line = s.pos_lnum in
  let column = s.pos_cnum - s.pos_bol + 1 in
  raise (Decls.Non_Wellformed(msg, line, column))

let mkTerm_with_pos startp endp d : Term.t =
  let lp pos = {
    Location.line = pos.pos_lnum; 
    Location.column = pos.pos_cnum - pos.pos_bol + 1 } in
  { Term.desc = d; 
    loc = Some{Location.start_pos = lp startp; 
               Location.end_pos = lp endp } } 

let mkTerm d : Term.t =
  let s = Parsing.symbol_start_pos () in 
  let e = Parsing.symbol_end_pos () in 
  mkTerm_with_pos s e d

let mkTerm_rhs i d : Term.t =
  let s = Parsing.rhs_start_pos i in 
  let e = Parsing.rhs_end_pos i in 
  mkTerm_with_pos s e d

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
      let vs = Term.all_vars t in
      let z = Vargen.mkVarGenerator "u" ~avoid:vs () in
      z, 
      mkTerm (BindW((mkTerm (Var z),  Basetype.newty Basetype.OneW), (unusable_var, t)))
    | PatVar(z) -> z, t
    | PatPair(p1, p2) ->
      let z1, t1 = elim p1 t in     
      let z2, t2 = elim p2 t1 in
      z1, Term.subst (mkSndW (mkVar z1)) z2 
            (Term.subst (mkFstW (mkVar z1)) z1 t2) in
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

%token LBRACE RBRACE LPAREN RPAREN LANGLE RANGLE
%token PLUS MINUS TIMES DIV
%token ENCODE DECODE
%token HAT COMMA TILDE QUOTE DOUBLEQUOTE COLON
%token SEMICOLON SHARP EQUALS TO VERTBAR
%token FN LAMBDA TYPE UNIT PUSH POP BOX UNBOX CALL NAT 
%token IF THEN ELSE PRINT HACK LET AS OF IN 
%token COPY CASE EXTERNAL
%token <int> NUM
%token <string> IDENT 
%token <string> CONSTR 
%token <string> STRING 
%token EOF

%right SEMICOLON 
%left EQUALS 
%left PLUS MINUS
%left TIMES DIV
%nonassoc HAT TILDE 
%nonassoc THEN
%nonassoc VERTBAR

%start decls
%type <Decls.decls> decls
%type <Term.t> term
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
          | PatVar(x) -> TermDecl(x, $4)
          | _ -> illformed "Variable declaration expected."
        }
    | LET pattern COLON inttype EQUALS term
        { clear_type_vars (); 
          match $2 with
          | PatVar(x) -> TermDecl(x, mkTerm (TypeAnnot($6, $4)))
          | _ -> illformed "Variable declaration expected."
        }
    | FN identifier pattern LBRACE term RBRACE
        { clear_type_vars (); 
          let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern $3 $5 in
          let def = mkTerm (LambdaW((x, alpha), t)) in
          TermDecl($2, def) }

identifier:
    | IDENT
        { $1 }

term:    
    | LAMBDA identifier TO term 
        { let alpha = Basetype.newty Basetype.Var in
          let ty = Type.newty Type.Var in
          mkTerm (LambdaU(($2, alpha, ty), $4)) }
    | LAMBDA LPAREN identifier COLON inttype RPAREN TO term 
        { let alpha = Basetype.newty Basetype.Var in
          mkTerm (LambdaU (($3, alpha, $5), $8)) }
    | FN pattern LBRACE term RBRACE
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern $2 $4 in
          mkTerm (LambdaW((x, alpha), t)) }
    | COPY term AS identifier COMMA identifier IN term
       { mkTerm (CopyU($2, ($4, $6, $8))) }
    | LET pattern EQUALS term IN term
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern $2 $6 in
          mkTerm (BindW(($4, alpha), (x, t))) }
    | IF term THEN term ELSE term
        { mkTerm (Case(Basetype.Data.boolid, [], $2,
                        [(unusable_var, $4); (unusable_var, $6)])) }
    | CASE term OF term_cases
        {let id, c = $4 in
         let sorted_c = List.sort ~cmp:(fun (i, _, _) (j, _, _) -> compare i j) c in
         let indices = List.map ~f:(fun (i, _, _) -> i) sorted_c in
         let cases = List.map ~f:(fun (_, x, t) -> (x, t)) sorted_c in
         let n = List.length (Basetype.Data.constructor_names id) in
         let params = List.init 
                        (Basetype.Data.params id)
                        ~f:(fun _ -> Basetype.newtyvar ()) in
         (* Check that there is a case for all constructors *)
         if (indices = List.init n ~f:(fun i -> i)) then
           mkTerm (Case(id, params, $2, cases))
         else
           illformed "case must match each constructor exactly once!"
       }
    | term_app SEMICOLON term
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern PatUnit $3 in
          mkTerm (BindW(($1, alpha), (x, t))) }
    | term_binop EQUALS term_binop
        { let alpha = Basetype.newty Basetype.Var in
          let beta = Basetype.newty Basetype.Var in
          mkTerm (App(mkTerm (ConstW(Cinteq)), Type.newty Type.Var, mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_binop LANGLE term_binop
        { let alpha = Basetype.newty Basetype.Var in
          let beta = Basetype.newty Basetype.Var in
          mkTerm (App(mkTerm (ConstW(Cintslt)), Type.newty Type.Var, mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_binop
       { $1 } 
    | term_constr  
       { let alpha = Basetype.newty Basetype.Var in
         let id, i = $1 in mkTerm (InW((id, i,  mkTerm (UnitW)), alpha)) }
    | term_constr term_atom
       { let alpha = Basetype.newty Basetype.Var in
         let id, i = $1 in mkTerm (InW((id, i, $2), alpha)) }
    | BOX term_atom
       { let alpha = Basetype.newty Basetype.Var in
         mkTerm (Box($2, alpha)) }
    | UNBOX term_atom
       { let alpha = Basetype.newty Basetype.Var in
         mkTerm (Unbox($2, alpha)) }

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

term_binop:
    | term_binop PLUS term_binop
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
         mkTerm (App(mkTerm_rhs 2 (ConstW(Cintadd)), 
                     Type.newty Type.Var, 
                     mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_binop MINUS term_binop
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
         mkTerm (App(mkTerm_rhs 2 (ConstW(Cintsub)), 
                     Type.newty Type.Var, 
                     mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_binop TIMES term_binop
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
         mkTerm (App(mkTerm_rhs 2 (ConstW(Cintmul)), 
                     Type.newty Type.Var, 
                     mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_binop DIV term_binop
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
         mkTerm (App(mkTerm_rhs 2 (ConstW(Cintdiv)), 
                     Type.newty Type.Var, 
                     mkTerm (PairW(($1, alpha), ($3, beta))))) }
    | term_app
       { $1 }

term_app:
    | term_atom
       { $1 }
    | term_app term_atom 
       { mkTerm (App($1, Type.newty Type.Var, $2))  }

term_atom:
    | identifier
       { mkTerm (Term.Var($1)) }
    | LPAREN RPAREN 
       { mkTerm UnitW }
    | LPAREN term RPAREN
       { $2 }
    | LBRACE term RBRACE
        { let alpha = Basetype.newty Basetype.Var in
          let x, t = elim_pattern PatUnit $2 in
          mkTerm (LambdaW((x, alpha), t)) }
    | LPAREN term COMMA term RPAREN
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
         mkTerm (PairW(($2, alpha), ($4, beta))) }
    | NUM
       { mkTerm (ValW(Cintconst($1))) } 
    | PRINT term_atom
       { mkTerm (App(mkTerm (ConstW(Cintprint)), Type.newty Type.Var, $2)) }
    | ENCODE term_atom
       { let alpha = Basetype.newty Basetype.Var in
         let beta = Basetype.newty Basetype.Var in
          mkTerm (App(mkTerm (ConstW(Cencode(alpha, beta))), Type.newty Type.Var, $2)) }
    | DECODE LPAREN basetype COMMA term RPAREN
       { let alpha = Basetype.newty Basetype.Var in
          mkTerm (App(mkTerm (ConstW(Cdecode(alpha, $3))), Type.newty Type.Var, $5)) }
    | PUSH LPAREN basetype COMMA term RPAREN
        { mkTerm (App(mkTerm (ConstW(Cpush($3))), Type.newty Type.Var, $5)) }
    | POP LPAREN basetype RPAREN
        { mkTerm (App(mkTerm (ConstW(Cpop($3))), Type.newty Type.Var, mkTerm UnitW)) }
    | CALL LPAREN identifier COLON basetype TO basetype COMMA term RPAREN
        { mkTerm (App(mkTerm (ConstW(Ccall($3, $5, $7))), Type.newty Type.Var, $9)) }
    | HACK LPAREN term COLON inttype RPAREN
       { mkTerm (HackU($5, $3)) }
    | EXTERNAL LPAREN identifier COLON inttype RPAREN
        { mkTerm (ExternalU(($3, $5), Type.newty Type.Var)) }
    | PRINT STRING
       { mkTerm (App(mkTerm (ConstW(Cprint $2)), Type.newty Type.Var, mkTerm (UnitW))) }
//    | BOX LPAREN term RPAREN
//       { let alpha = Basetype.newty Basetype.Var in
//         mkTerm (Box($3, alpha)) }
//    | UNBOX LPAREN term RPAREN
//       { let alpha = Basetype.newty Basetype.Var in
//         mkTerm (Unbox($3, alpha)) }

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
      { Basetype.newty (Basetype.DataW(Basetype.Data.sumid 2, [$1; $3])) }

basetype_factor:
    | basetype_atom
      { $1 }
    | basetype_factor TIMES basetype_atom
      { Basetype.newty (Basetype.TensorW($1, $3)) }

basetype_atom:
    | QUOTE identifier
      { basetype_var $2 }
    | UNIT
      { Basetype.newty (Basetype.OneW) }
    | NAT
      { Basetype.newty (Basetype.NatW) }
    | BOX LANGLE basetype RANGLE
      { Basetype.newty (Basetype.BoxW($3)) }
    | identifier
      { Basetype.newty (Basetype.DataW($1, [])) }
    | identifier LANGLE basetype_list RANGLE 
      { Basetype.newty (Basetype.DataW($1, $3)) }
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
    | LBRACE basetype RBRACE VERTBAR inttype VERTBAR TO inttype
      { Type.newty (Type.FunU($2, $5, $8)) } 
  /*  | VERTBAR inttype VERTBAR TO inttype
      { Type.newty (Type.FunU(Basetype.newtyvar(), $2, $5)) } */
    | inttype_factor TO inttype
      { Type.newty (Type.FunU(Basetype.newty Basetype.Var, $1, $3)) }

inttype_factor:
    | inttype_atom
      { $1 }

inttype_atom:
    | DOUBLEQUOTE identifier
      { type_var $2 }
    | basetype TO basetype 
      {  Type.newty (Type.FunW($1, $3)) }
    | LPAREN inttype RPAREN
      { $2 }
%%
