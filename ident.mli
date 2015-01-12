open Core.Std

(** Variable names *)

module T : sig
  
  type t = private {
    name: string;
    index: int
  } with sexp

  val hash: t -> int
end

include T
include Comparable.S with type t := t
module Table : Hashtbl.S with type key := t
  
val global: string -> t  
val fresh: string -> t  
val variant: t -> t

val to_string: t -> string

