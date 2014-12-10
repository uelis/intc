(** Generation of fresh variables *)

(** The call [mkVarGenerator x ~avoid:xs] constructs a variable
    generator that makes fresh variables named similarly to [x]
    (including [x] itself) and that is guaranteed to avoid the
    names in [xs]. *)
val mkVarGenerator: string -> avoid: string list -> unit -> string
