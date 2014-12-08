(** Type inference *)

(** Type contexts *)
type 'a context = (Term.var * 'a) list

(** Split a context into the part declaring the exactly the 
    free variables of a term and the rest.
    The call [take_subcontext gamma t] returns [(gamma1, gamma2)],
    where [gamma1] declares all the free variables of [t] and
    [gamma2] contains the rest of the variables. *)
val take_subcontext : 'a context -> Term.t -> 'a context * 'a context

(** Given a context [gamma] and two terms [t1] and [t2], split the context 
    into [(gamma1, gamma2)], such that [gamma1] contains just free variables
    from [t1] and [gamma2] contains just variables from [t2]. If a variable
    appears in both terms, then it may appear in either [gamma1] or [gamma2], 
    but not in both. *)
val split_context : 'a context -> Term.t -> Term.t -> 'a context * 'a context

exception Typing_error of Term.t option * string

(** Compute the principal type of a value term.
    Type variables are unified as a side effect.
    Type error is indicated by raising [Typing_error] with the offending
    term and reason. *)
val principal_type_value: Basetype.t context -> Term.t -> Basetype.t

(** Compute the principal type of an interactive term.
    Type variables are unified as a side effect.
    Type error is indicated by raising [Typing_error] with the offending
    term and reason. *)
val principal_type: Basetype.t context -> Type.t context -> Term.t -> Type.t
