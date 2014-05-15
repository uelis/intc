open Core.Std

module type Repr = sig 
  type t 
  type desc

  val phys_id : t -> int
  val next_mark : unit -> int                      
  val set_mark : t -> int -> unit
  val get_mark : t -> int

  val newty : desc -> t
  val children: t -> t list

  val find : t -> t
  val finddesc : t -> desc
  val union : t -> t -> unit
  val equals : t -> t -> bool
end

module type S = sig

  type t

  val dfs_cycles: t -> int list
  val is_acyclic : t -> bool

end

module Algs(R : Repr) : S with type t := R.t

