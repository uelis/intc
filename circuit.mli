type wire = {
  src: int;
  dst: int;
  type_forward: Basetype.t;
  type_back: Basetype.t
}

val map_wire : (int -> int) -> wire -> wire                 

type instruction =
  | Axiom of wire (* fn () -> f *) * (Term.var list * (Term.var * Term.t))
  | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
  | Der of wire (* \Tens A X *) * wire (* X *) * (Term.var list * Term.t)
  | Case of Basetype.Data.id * Basetype.t list * wire * (wire list)
  | Door of wire (* X *) * wire (* \Tens A X *)
  | Assoc of wire (* \Tens (A x B) X *) * wire (* \Tens A (\Tens B X) *) 
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B <= A *)
  | Bind of wire (* (\Tens A (1 => B))^* *) * wire (* A => B *)
  | Seq of wire (* (A=>B)^* *) * wire (* (B=>C)^* *) * wire (* A=>C *)

val map_instruction : (int -> int) -> instruction -> instruction                  
val wires : instruction list -> wire list

(* Behaviour of LWeak *)
val embed : Basetype.t -> Basetype.t -> Term.t -> Term.t
val project : Basetype.t -> Basetype.t -> Term.t -> Term.t

type t = { 
  output : wire; 
  instructions : instruction list
}

val circuit_of_termU : Term.t -> t

val dot_of_circuit :
 ?title:string -> ?wire_style:(wire -> string) -> t -> string
