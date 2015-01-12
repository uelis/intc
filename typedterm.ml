open Core.Std

type value_const = Ast.value_const
type op_const = Ast.op_const

(** Value terms *)
type value = {
  value_desc: v_desc;
  value_type: Basetype.t;
  value_loc: Ast.Location.t
} and v_desc =
  | VarV of Ident.t
  | ConstV of value_const
  | UnitV
  | PairV of value * value
  | FstV of value
  | SndV of value
  | InV of Basetype.Data.id * int * value
  | SelectV of Basetype.Data.id * (Basetype.t list) * value * int

(** Interaction terms *)
type t = {
  t_desc: t_desc;
  t_type: Type.t;
  t_context: (Ident.t * Type.t) list;
  t_loc: Ast.Location.t
} and t_desc =
  | Var of Ident.t
  | Const of op_const
  | Return of value
  | Bind of (t * Basetype.t) * (Ident.t * t)
  | Fn of (Ident.t * Basetype.t) * t
  | Fun of (Ident.t * Basetype.t * Type.t) * t
  | AppV of t * value
  | AppI of t * t
  | Case of Basetype.Data.id * (Basetype.t list) * value * ((Ident.t * t) list)
  | Copy of t * (Ident.t list * t)
  | Pair of t * t
  | LetPair of t* ((Ident.t * Type.t) * (Ident.t * Type.t) * t)
  | Direct of Type.t * t
