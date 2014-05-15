(** Pretty printing of terms and types *)

(** Resets all previously chosen variable names for type variables
    etc. *)
val reset_names : unit -> unit

(** Returns a string representation of the data type with the given
    name. *) 
val string_of_data : string -> string

val string_of_basetype : Basetype.t -> string
val string_of_type : ?concise:bool -> Type.t -> string

val string_of_op_const : Term.op_const -> string

val print_term : Term.t -> unit
val string_of_term : Term.t -> string
