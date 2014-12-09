(** Compilation of source programs to interaction circuits 

    Circuits are repesented by lists of nodes, which each 
    lists the edges (here: wires) that it is connected to.
*)

(** A wire is specified by its two end-points, which are
    identified using numbers. The number uniquely specify
    the end-points, i.e. no number may appear in two nodes.
    The wire also specifies the message passing types for
    forward passing ([src] to [dst]) and backwards ([dst] to
    [src]). *)
type wire = {
  src: int;
  dst: int;
  type_forward: Basetype.t;
  type_back: Basetype.t
}

(* Instructions are graph nodes. The wires mentioned in each node
   are meant to be connected to the node with its [src] end.*)
type instruction =
  | Base of wire (* TA *) * (Term.var list * Term.t)
  | Seq of wire (* (TA)^* *) * wire (* \Tens A (TB)^* *) * wire (* TB *)
  | Encode of wire (* A => B *)
  | Decode of wire (* B => A *)
  | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
  | Der of wire (* \Tens A X *) * wire (* X *) * (Term.var list * Term.t)
  | Case of Basetype.Data.id * Basetype.t list * wire * (wire list)
  | Door of wire (* X *) * wire (* \Tens A X *)
  | Assoc of wire (* \Tens (A x B) X *) * wire (* \Tens A (\Tens B X) *)
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B \lhd A *)
  | Bind of wire (* \Tens A X *) * wire (* (A => X) *)
  | App of wire (* (A => X) *) * (Term.var list * Term.t) * wire (* X *)
  | Direct of wire (* (X- => TX+)^* *) * wire (* X *)

(** Returns the wires anchored at a node *)
val wires : instruction -> wire list

(** The node [LWeak] depends on the choice of an embedding-projection
    pair. There are many possible choices. The following 
    pairs are sufficient for the translation given below. *)
val embed : Basetype.t -> Basetype.t -> Term.t -> Term.t
val project : Basetype.t -> Basetype.t -> Term.t -> Term.t

(** Circuits are a list of instruction node with a choice of output wire.
*)
type t = { 
  output : wire; 
  instructions : instruction list
}

(** Translate a well-typed term into a circuit. *)
val circuit_of_term : Term.t -> t

(** Convert a circuit to dot format for debugging. *)
val dot_of_circuit :
 ?title:string -> ?wire_style:(wire -> string) -> t -> string
