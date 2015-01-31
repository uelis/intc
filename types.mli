(** General algorithms for types represented by a union find data
    structure. *)
open Core.Std

module type Repr = sig
  type t
  type desc

  (** Unique physical id of type. *)
  val phys_id : t -> int

  (** Compute a fresh mark. *)
  val next_mark : unit -> int

  (** Set the mark to a type. Each node in the syntax tree of a type
      is assumed to be marked. *)
  val set_mark : t -> int -> unit

  (** Returns the mark of a type. *)
  val get_mark : t -> int

  (** Construct a fresh syntax tree node with the given description.
      The description may contain references to the children. *)
  val newty : desc -> t

  (** Returns the children of the node. *)
  val children: t -> t list

  (** Returns the unique (wrt. physical equality) representative of
      the set of types in which the given type is containted. This is
      the find operation of union-find. *)
  val find : t -> t

  (** [finddesc x] return the description of the node [find x]. *)
  val finddesc : t -> desc

  (** Take the union of two nodes, i.e. the union in union-find.
      [union t1 t2] causes [t1] to be linked to [t2].
   *)
  val union : t -> t -> unit

  (** Equality of types. *)
  val equals : t -> t -> bool
end

module type S = sig

  type t

  val dfs_cycles: t -> int list
  val is_acyclic : t -> bool

end

module Algs(R : Repr) : S with type t := R.t
