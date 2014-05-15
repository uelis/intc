(** Canonisation of source terms 
 
    TODO: document what a canonical term is.
*)

(** Canonises a term.
    Expects a term that has had type information filled in by
    type inference. The resulting term will have this type information
    as well, so type inference does not need to be performed again *)
val canonise : Term.t -> Term.t
