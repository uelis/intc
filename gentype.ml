open Core.Std
       
exception Constructor_mismatch
exception Cyclic_type

module type Typesgn = sig
  type 'a t with sexp

  val map: ('a -> 'b) -> 'a t -> 'b t
  val children: 'a t -> 'a list

  val equals: 'a t -> 'a t -> equals:('a -> 'a -> bool) -> bool
    
  val unify_exn: 'a t -> 'a t -> unify:('a -> 'a -> unit) -> unit
end

module type S = sig
  type t with sexp

  module Sgn: Typesgn
    
  type 'a var_or_sgn =
    | Var
    | Sgn of 'a Sgn.t

  val repr_id : t -> int
  
  val newvar : unit -> t

  (** Construct a fresh syntax tree node with the given description.
      The description may contain references to the children. *)
  val newty : t Sgn.t -> t
  
  val free_vars: t -> t list

  val freshen: t -> t
    
  val freshen_list: t list -> t list

  val replace_by_fresh_var: t -> unit

  val subst: t -> (t -> t) -> t

  (** [case x] return the description of the node [find x]. *)
  val case : t -> t var_or_sgn

  val identical : t -> t -> bool

  (** Equality of types. *)
  val equals : t -> t -> bool

  val unify_exn : t -> t -> unit
    
  val dfs_cycles: t -> t list
                         
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

  let next_id = ref 0
                  
  let newD d =
    incr next_id;
    { desc = D d; mark = 0; id = !next_id }
  let newty s = newD (Sgn s)
  let newvar () = newD Var

  let phys_id t = t.id

  let current_mark : int ref = ref 0
  let next_mark () : int = incr current_mark; !current_mark

  let set_mark t i =
    t.mark <- i

  let get_mark t =
    t.mark

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

  type type_t = t with sexp

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

  let identical (u: t) (v: t) : bool =
    phys_id u = phys_id v
      
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

  let replace_by_fresh_var t =
    let a = newvar () in
    (find t).desc <- Link a
      
  let dfs_cycles t =
    let cycles = Int.Table.create () in
    let mark_open = next_mark () in
    let mark_done = next_mark () in
    let rec dfs (a: t) =
      let r = find a in
      if get_mark r = mark_open then
        Int.Table.replace cycles ~key:(phys_id r) ~data:r
      else if (get_mark r = mark_done) then
        ()
      else begin
        set_mark r mark_open;
        List.iter (children r) ~f:dfs;
        set_mark r mark_done
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
      | Var, _ ->
        union c1 c2
      | _, Var ->
        union c2 c1
      | Sgn d1, Sgn d2 ->
        T.unify_exn d1 d2 ~unify:unify_raw
          
  let check_cycle (b: t) : unit =
    if not (is_acyclic b) then
      raise Cyclic_type
        
  let unify_exn (b1 : t) (b2 : t) : unit =
    unify_raw b1 b2;
    check_cycle b1
end
