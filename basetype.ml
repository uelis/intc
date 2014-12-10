open Core.Std

type t =
   { mutable desc : desc;
     mutable mark : int;
     id : int
   }
and desc =
  | Link of t
  | Var
  | IntB
  | ZeroB
  | UnitB
  | BoxB of t
  | PairB of t * t
  | DataB of string * t list
with sexp

let next_id = ref 0
let newty d =
  incr next_id; { desc = d; mark = 0; id = !next_id }
let newtyvar () =
  newty Var

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

let finddesc (t : t) = (find t).desc

let union (t1 : t) (t2 : t) : unit =
  (find t1).desc <- Link (find t2)

type type_t = t with sexp

let children a =
  match finddesc a with
  | Var | IntB | ZeroB | UnitB -> []
  | BoxB(b1) -> [b1]
  | PairB(b1, b2) -> [b1; b2]
  | DataB(_, bs) -> bs
  | Link _ -> assert false

let rec free_vars (b: t) : t list =
  match (find b).desc with
    | Var -> [find b]
    | IntB | ZeroB | UnitB -> []
    | BoxB(b1) -> free_vars b1
    | PairB(b1, b2) -> free_vars b1 @ (free_vars b2)
    | DataB(_, bs) -> List.concat (List.map ~f:free_vars bs)
    | Link _ -> assert false

let rec subst (f: t -> t) (b: t) : t =
  match (find b).desc with
    | Var -> f (find b)
    | IntB -> newty IntB
    | ZeroB -> newty ZeroB
    | UnitB -> newty UnitB
    | BoxB(b1) -> newty(BoxB(subst f b1))
    | PairB(b1, b2) -> newty(PairB(subst f b1, subst f b2))
    | DataB(id, bs) -> newty(DataB(id, List.map ~f:(subst f) bs))
    | Link _ -> assert false

let rec equals (u: t) (v: t) : bool =
  let ur = find u in
  let vr = find v in
    if ur.id = vr.id then true
    else
      match ur.desc, vr.desc with
        | Var, Var ->
            false
        | IntB, IntB | ZeroB, ZeroB | UnitB, UnitB ->
            true
        | BoxB(u1), BoxB(v1)  ->
            equals u1 v1
        | PairB(u1, u2), PairB(v1, v2)  ->
            equals u1 v1 && equals u2 v2
        | DataB(idu, lu), DataB(idv, lv) ->
            idu = idv &&
            List.for_all2_exn lu lv ~f:equals
        | Link _, _ | _, Link _ -> assert false
        | Var, _ | IntB, _ | ZeroB, _ | UnitB, _
        | BoxB _, _ | PairB _ , _ | DataB _ , _ ->
            false

let freshen_list ts =
  let vm = Int.Table.create () in
  let fv x =
    match Int.Table.find vm (find x).id with
    | Some y -> y
    | None ->
      let y = newty Var in
      Int.Table.replace vm ~key:(find x).id ~data:y;
      y in
    List.map ts ~f:(subst fv)

let freshen t =
  match freshen_list [t] with
    | [f] -> f
    | _ -> assert false


module Data =
struct
  type id = string

  (* Type variables in the params list must remain private to this module *)
  type d = { name : string;
             params : t list;
             discriminated: bool;
             constructors : (string * t) list }

  let datatypes = String.Table.create ()
  let boolid =
    String.Table.replace datatypes
      ~key:"bool"
      ~data:{ name = "bool";
              params = [];
              discriminated = true;
              constructors = ["True", newty UnitB;
                              "False", newty UnitB] };
    "bool"

  let sumid =
    let sumtypes = Int.Table.create () in
    fun (n : int) ->
      match Int.Table.find sumtypes n with
      | Some id -> id
      | None ->
        let name = "sum" ^ (string_of_int n) in
        let l = List.init n ~f:(fun i -> i, newty Var) in
        let params = List.map ~f:snd l in
        let constructors =
          List.map l
            ~f:(fun (i, alpha) ->
              (if n = 2 && i = 0 then "Inl"
               else if n = 2 && i = 1 then "Inr"
               else Printf.sprintf "In_%i_%i" n i),
              alpha) in
        let d = { name = name;
                  params = params;
                  discriminated = true;
                  constructors = constructors } in
        String.Table.replace datatypes ~key:name ~data:d;
        Int.Table.replace sumtypes ~key:n ~data:name;
        name

  let fresh_id basename =
    let used_names = String.Table.keys datatypes in
    Vargen.mkVarGenerator basename ~avoid:used_names ()

  (* declare nullary and binary sums by default; all others are declared on demand *)
  let _ = ignore (sumid 0); ignore (sumid 2)

  let params id = List.length (String.Table.find_exn datatypes id).params

  let constructor_count id =
    let cs = (String.Table.find_exn datatypes id).constructors in
      List.length cs

  let constructor_names id =
    let cs = (String.Table.find_exn datatypes id).constructors in
      List.map cs ~f:fst

  let constructor_types id newparams =
    let cs = (String.Table.find_exn datatypes id).constructors in
    let ts = List.map cs ~f:snd in
    let ps = (String.Table.find_exn datatypes id).params in
    assert (List.length ps = List.length newparams);
    let param_subst alpha =
      let l = List.zip_exn ps newparams in
      List.Assoc.find l alpha
      |> Option.value ~default:alpha in
    List.map ~f:(subst param_subst) ts

  let is_discriminated id =
    (String.Table.find_exn datatypes id).discriminated

  let is_recursive id =
    let rec check_rec a =
      match finddesc a with
        | Var | ZeroB | UnitB | IntB -> false
        | BoxB(b1) -> check_rec b1
        | PairB(b1, b2) -> check_rec b1 && check_rec b2
        | DataB(id', bs) -> id = id' || List.exists ~f:check_rec bs
        | Link _ -> assert false in
    let freshparams = List.init (params id) ~f:(fun _ -> newty Var) in
    let ct = constructor_types id freshparams in
    List.exists ~f:check_rec ct

  exception Found of id * int

  let find_constructor name =
    try
      String.Table.iter datatypes
        ~f:(fun ~key:id ~data:d ->
          Array.of_list d.constructors
          |> Array.iteri ~f:(fun i (cname, _) ->
            if cname = name then raise (Found (id, i)))
        );
        raise Not_found
    with Found (id, i) -> id, i

  let make name ~nparams:nparams ~discriminated:discriminated =
    String.Table.replace datatypes ~key:name
      ~data:{ name = name;
              (* (these type variables must remain private) *)
              params = List.init nparams ~f:(fun _ -> newty Var);
              discriminated = discriminated;
              constructors = [] }

  (* Preconditions:
   *  - No constructor called name is already defined.
   *  - The free type variables in argtype are contained
   *    in paramvars.
   *)
  let add_constructor id name paramvars argtype =

    (* check if constructor is already defined *)
    begin
      try
        ignore (find_constructor name);
        failwith "Duplicate constructor definition"
      with Not_found -> ()
    end;
    let d = Hashtbl.find_exn datatypes id in

    (* check that free variables in argtype are contained in
     * paramvars. *)
    let ftv = free_vars argtype in
    if List.exists
         ~f:(fun alpha ->
           not (List.exists paramvars
                  ~f:(fun beta -> equals alpha beta) ))
         ftv then
      failwith ("The free variables in any constructor must be " ^
                "contained in the type parameters.");

    (* check that all recursive occurrences of the type are under a box. *)
    let rec check_rec_occ a =
      match finddesc a with
      | Var | IntB | UnitB | ZeroB -> ()
      | PairB(a1, a2) ->
        check_rec_occ a1;
        check_rec_occ a2
      | DataB(id', params) ->
        if (id = id') then
          failwith "Recursive occurrences are only allowed within box<...>"
        else
          List.iter params ~f:check_rec_occ
      | BoxB _ -> ()
      | Link _ -> assert false
    in
    check_rec_occ argtype;

    (* replace given parameters by private parameters *)
    let param_subst alpha =
      let l = List.zip_exn paramvars d.params in
      List.Assoc.find l alpha
      |> Option.value ~default:alpha in
    let argtype' = subst param_subst argtype in
    let d' = { d with constructors = d.constructors @ [name, argtype'] } in
    String.Table.replace datatypes ~key:id ~data:d'
end
