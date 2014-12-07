type wire = {
  src: int;
  dst: int;
  type_forward: Basetype.t;
  type_back: Basetype.t
}

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
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B <= A *)
  | Bind of wire (* \Tens A X *) * wire (* (A => X) *)
  | App of wire (* (A => X) *) * (Term.var list * Term.t) * wire (* X *)
  | Direct of wire (* (X- => TX+)^* *) * wire (* X *)

val wires : instruction -> wire list

(* Behaviour of LWeak *)
val embed : Basetype.t -> Basetype.t -> Term.t -> Term.t
val project : Basetype.t -> Basetype.t -> Term.t -> Term.t

type t = { 
  output : wire; 
  instructions : instruction list
}

val circuit_of_term : Term.t -> t

val dot_of_circuit :
 ?title:string -> ?wire_style:(wire -> string) -> t -> string
