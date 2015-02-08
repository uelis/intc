open Core.Std
       
exception Constructor_mismatch
exception Cyclic_type

(** Signature of type constructors *)
module type Typesgn = sig
  
  (** Constructors over values of type ['a].
      For a type with nat and functions, the signature would be
      [type 'a t = Nat | Fun of 'a * 'a].
  *)
  type 'a t with sexp
  
  val map: ('a -> 'b) -> 'a t -> 'b t
                                   
  val children: 'a t -> 'a list

  val equals: 'a t -> 'a t -> equals:('a -> 'a -> bool) -> bool

  (** Unification of consructors.
      May raise the exceptions [Constructor_mismatch] or [Cyclic_type].
  *)
  val unify_exn: 'a t -> 'a t -> unify:('a -> 'a -> unit) -> unit
end

module type S = sig
  type t with sexp

  (** Signature of type constructors. *)
  module Sgn: Typesgn

  (** A variable or type constructor from the signature. *)
  type 'a var_or_sgn =
    | Var
    | Sgn of 'a Sgn.t

  (** Unique representation id of each type.
      This id may change over time, e.g. because of unification.
  *)
  val repr_id : t -> int

  (** Construct a new type variable. *)
  val newvar : unit -> t

  (** Construct a type from a given constructor application. *)
  val newty : t Sgn.t -> t
  
  (** Type variables in type. *)
  val free_vars: t -> t list

  (** Rename each type variable in the given type with a fresh name. *)
  val freshen: t -> t

  (** Rename each type variable in the given types with a fresh name.
      If a variable appears more than once in the list, then it will be
      renamed to the same fresh name. *)
  val freshen_list: t list -> t list

  (** Delete the given type and replace it by a fresh type variable. *)
  val replace_by: t -> t -> unit

  (** Substitution. 
      The call [subst a f] applies [f] to all variables in [a]. *)
  val subst: t -> (t -> t) -> t

  (** [case x] returns whether the root of the syntax tree represented by [x]
      is a variable or signature constructor. *)
  val case : t -> t var_or_sgn

  (** Equality of types. Checks if two types repesent the same syntax tree. *)
  val equals : t -> t -> bool

  (** Unification of types.
      May raise the exceptions [Constructor_mismatch] or [Cyclic_type].*)
  val unify_exn : t -> t -> unit
    
  (** Finds the points where a dfs walk in the syntax tree returns to an
      already visited node.
      Unification performs a circularity check. If a circular type is found,
      exception [Cyclic_type] is raised and the type will be left cyclic, e.g.
      for error reporting. 
  *)
  val dfs_cycles: t -> t list
                         
  (** Checks if type is a syntax tree. *)
  val is_acyclic : t -> bool
end

module Make(T: Typesgn) = struct

  module Sgn = T
    
  type 'a var_or_sgn =
    | Var
    | Sgn of 'a T.t
  with sexp

  type t =
    { mutable desc : desc;
      mutable mark : int;
      id : int
    }
  and desc =
    | Link of t
    | D of (t var_or_sgn)
  with sexp
                  
  let newD =
    let next_id = ref 0 in
    fun d ->
      incr next_id;
      { desc = D d; mark = 0; id = !next_id }
      
  let newty s = newD (Sgn s)
  let newvar () = newD Var

  let next_mark : unit -> int =
    let current_mark : int ref = ref 0 in
    fun () ->
      incr current_mark;
      !current_mark

  let rec find (t : t) : t =
    match t.desc with
    | Link l ->
      let r = find l
      in t.desc <- Link r;
      r
    | _ -> t
      
  let repr_id t = (find t).id

  let case (t: t) : t var_or_sgn =
    match (find t).desc with
    | D d -> d
    | Link _ -> assert false

  let union (t1 : t) (t2 : t) : unit =
    (find t1).desc <- Link (find t2)

  let children a =
    match case a with
    | Var -> []
    | Sgn d -> T.children d

  let rec free_vars (b: t) : t list =
    match case b with
    | Var -> [find b]
    | Sgn d ->
      d |> T.map free_vars |> T.children |> List.concat

  let rec subst (b: t) (f: t -> t) : t =
    match case b with
    | Var -> f (find b)
    | Sgn d -> newty (T.map (fun a -> subst a f) d)

  let rec equals (u: t) (v: t) : bool =
    let ur = find u in
    let vr = find v in
    if ur.id = vr.id then true
    else
      match ur.desc, vr.desc with
      | D Var, _ | _, D Var -> false
      | D (Sgn d), D (Sgn e) -> T.equals d e ~equals:equals
      | _, Link _ | Link _, _ -> assert false

  let freshen_list ts =
    let vm = Int.Table.create () in
    let fv x =
      match Int.Table.find vm (find x).id with
      | Some y -> y
      | None ->
        let y = newvar () in
        Int.Table.replace vm ~key:(find x).id ~data:y;
        y in
    List.map ts ~f:(fun a -> subst a fv)

  let freshen t =
    match freshen_list [t] with
    | [f] -> f
    | _ -> assert false

  let replace_by t1 t2 =
    (find t1).desc <- Link t2
      
  let dfs_cycles t =
    let cycles = Int.Table.create () in
    let mark_open = next_mark () in
    let mark_done = next_mark () in
    let rec dfs (a: t) =
      let r = find a in
      if r.mark = mark_open then
        Int.Table.replace cycles ~key:(r.id) ~data:r
      else if (r.mark = mark_done) then
        ()
      else begin
        r.mark <- mark_open;
        List.iter (children r) ~f:dfs;
        r.mark <- mark_done
      end in
    dfs t;
    let keys = Int.Table.fold cycles
                 ~f:(fun ~key:_ ~data:t ts -> t :: ts) ~init:[] in
    keys

  let is_acyclic t =
    dfs_cycles t = []
      
  let rec unify_raw (b1: t) (b2: t) : unit =
    let c1, c2 = find b1, find b2 in
    if not (phys_equal c1 c2) then
      match case c1, case c2 with
      | Var, _ -> union c1 c2
      | _, Var -> union c2 c1
      | Sgn d1, Sgn d2 -> T.unify_exn d1 d2 ~unify:unify_raw
          
  let check_cycle (b: t) : unit =
    if not (is_acyclic b) then
      raise Cyclic_type
        
  let unify_exn (b1 : t) (b2 : t) : unit =
    unify_raw b1 b2;
    check_cycle b1
end
