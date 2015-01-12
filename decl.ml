type t =
  | TermDecl of Ident.t * Ast.t

exception Illformed_decl of string * int * int

let expand_in_term (d: t) (s: Ast.t) : Ast.t =
  (* fsubst t v s substitutes t for v in s, such that each time t is
   * pasted all the type variables in t are replaced by fresh ones *)
  let rec fsubst t v s =
    match Ast.head_subst (Ast.freshen_type_vars t) v s with
      | Some s' -> fsubst t v s'
      | None -> s
  in
    match d with
      | TermDecl(v, t) -> fsubst t v s

let expand (d: t) : t -> t =
  function
    | TermDecl(w, s) -> TermDecl(w, expand_in_term d s)

let rec expand_all (ds: t list) : t list =
  match ds with
    | [] -> []
    | d :: rest ->
        d :: expand_all (List.map (expand d) rest)
