exception Non_Wellformed of string * int * int

type decl = 
  | TermDecl of Term.var * Term.t

type decls = decl list

let subst_decl_in_term (d: decl) (s: Term.t) : Term.t =
  (* fsubst t v s substitutes t for v in s, such that each time t is 
   * pasted all the type variables in t are replaced by fresh ones *)
  let rec fsubst t v s =
    match Term.head_subst (Term.freshen_type_vars t) v s with
      | Some s' -> fsubst t v s'
      | None -> s
  in 
    match d with
      | TermDecl(v, t) -> fsubst t v s

(* expands d in decl *)                                               
let subst_decl_in_decl (d: decl) : decl -> decl =
  function
    | TermDecl(w, s) -> TermDecl(w, subst_decl_in_term d s)

let rec subst_decls (ds: decls) : decls =
  match ds with 
    | [] -> []
    | d :: rest ->
        d :: subst_decls (List.map (subst_decl_in_decl d) rest)
