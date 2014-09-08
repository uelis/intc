open Core.Std

module type Repr = sig
  type t
  and desc

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

module Algs(R : Repr) = struct

  let dfs_cycles t =
    let cycles = Int.Table.create () in
    let mark_open = R.next_mark () in
    let mark_done = R.next_mark () in
    let rec dfs (a: R.t) =
      let r = R.find a in
      if R.get_mark r = mark_open then
        Int.Table.replace cycles ~key:(R.phys_id r) ~data:()
      else if (R.get_mark r = mark_done) then
        ()
      else begin
        R.set_mark r mark_open;
        List.iter (R.children r) ~f:dfs;
        R.set_mark r mark_done
      end in
    dfs t;
    let keys = Int.Table.fold cycles
                 ~f:(fun ~key:k ~data:_ ks -> k :: ks) ~init:[] in
    keys

  let is_acyclic t =
    dfs_cycles t = []
end
