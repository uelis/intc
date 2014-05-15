open Core.Std
(* The representation of types uses a union find data
 * structure that makes unification easy. 
 * I learned about this representation of types
 * from the following article (Section 1.4):
 *   Didier Rémy. Using, Understanding, and Unraveling
 *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
 *   http://pauillac.inria.fr/~remy/cours/appsem/
 *)

type t = 
   { mutable desc : desc; 
     mutable mark : int;
     id : int (* unique id *)
   }
and desc = 
  | Link of t
  | Var
  | NatW
  | ZeroW
  | OneW
  | BoxW of t
  | TensorW of t * t
  | DataW of string * t list
with sexp                        

include Types.Repr 
  with type t := t with type desc := desc

module Data: 
sig
  type id = string
  val sumid : int -> id
  val boolid : id
  val fresh_id : string -> id

  val params : id -> int
  val constructor_count : id -> int 
  val constructor_names : id -> string list 
  val constructor_types : id -> t list -> t list

  val is_recursive: id -> bool
  val is_discriminated: id -> bool
  val find_constructor: string -> id * int

  val make : id -> nparams:int -> discriminated:bool -> unit
  val add_constructor : id -> string -> t list -> t -> unit
end

val newtyvar: unit -> t

(** Returns the list of free type variables in their order of 
    appearance in the term, including duplicates *)
val free_vars: t -> t list                         
val subst: (t -> t) -> t -> t
val freshen: t -> t
val freshen_list: t list -> t list
