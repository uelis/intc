(** Variable names *)

open Core.Std

module T = struct
  
  type t = {
    name: string;
    index: int
  } with sexp

  let compare (x: t) (y: t): int =
    let i = String.compare x.name y.name in
    if i = 0 then Int.compare x.index y.index else i

  let hash (x: t) : int =
    String.hash x.name lxor x.index
end

include T
include Comparable.Make(T)
module Table = Hashtbl.Make(T)

let next_index = ref 0

let global (s: string) : t  =
  { name = s; index = 0 }

let fresh (s: string) : t  =
  incr next_index;
  { name = s; index = !next_index }

let variant (x: t) : t =
  incr next_index;
  { x with index = !next_index }

let to_string (x: t) : string =
  if Int.(=) x.index 0 then x.name else Printf.sprintf "%s$%i" x.name x.index
