open Core.Std

type 'a sgn =
  | EncodedB of 'a
  | IntB
  | ZeroB
  | UnitB
  | BoxB of 'a
  | ArrayB of 'a
  | PairB of 'a * 'a
  | DataB of string * 'a list
with sexp
    
module Sig = struct

  type 'a t = 'a sgn with sexp                  

  let map (f : 'a -> 'b) (t : 'a t) : 'b t =
    match t with
     | EncodedB x -> EncodedB (f x)
     | IntB  -> IntB
     | ZeroB  -> ZeroB
     | UnitB  -> UnitB
     | BoxB x -> BoxB (f x)
     | ArrayB x -> ArrayB (f x)
     | PairB(x, y) -> PairB(f x, f y)
     | DataB(id, xs) -> DataB(id, List.map ~f:f xs)

  let children (t: 'a t) : 'a list =
    match t with
     | EncodedB x -> [x]
     | IntB
     | ZeroB
     | UnitB -> []
     | BoxB x -> [x]
     | ArrayB x -> [x]
     | PairB(x, y) -> [x; y]
     | DataB(_, xs) -> xs

  let equals (s: 'a t) (t: 'a t) ~equals:(equals: 'a -> 'a -> bool) : bool =
    match s, t with
    | IntB, IntB
    | ZeroB, ZeroB
    | UnitB, UnitB ->
      true
    | EncodedB(t1), EncodedB(s1) 
    | BoxB(t1), BoxB(s1) 
    | ArrayB(t1), ArrayB(s1) ->
      equals t1 s1
    | PairB(t1, t2), PairB(s1, s2) ->
      equals t1 s1 && equals t2 s2
    | DataB(i, ts), DataB(j, ss) when i = j ->
      begin
        match List.zip ts ss with
        | None -> false
        | Some l -> List.for_all l ~f:(fun (t, s) -> equals t s)
      end
    | EncodedB _, _ | IntB, _ | ZeroB, _ | UnitB, _
    | BoxB _, _ | ArrayB _, _ | PairB _, _ | DataB _, _ ->
      false

  let unify_exn (s: 'a t) (t: 'a t) ~unify:(unify: 'a -> 'a -> unit) : unit =
    match s, t with
    | IntB, IntB
    | ZeroB, ZeroB
    | UnitB, UnitB ->
      ()
    | EncodedB(t1), EncodedB(s1) 
    | BoxB(t1), BoxB(s1) 
    | ArrayB(t1), ArrayB(s1) ->
      unify t1 s1
    | PairB(t1, t2), PairB(s1, s2) ->
      unify t1 s1;
      unify t2 s2
    | DataB(i, ts), DataB(j, ss) when i = j ->
      begin
        match List.zip ts ss with
        | None -> raise Uftype.Constructor_mismatch
        | Some l -> List.iter l ~f:(fun (t, s) -> unify t s)
      end
    | EncodedB _, _ | IntB, _ | ZeroB, _ | UnitB, _
    | BoxB _, _ | ArrayB _, _ | PairB _, _ | DataB _, _ ->
      raise Uftype.Constructor_mismatch
end

module Basetype = Uftype.Make(Sig)
include Basetype

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
        let l = List.init n ~f:(fun i -> i, newvar()) in
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

  (* declare nullary and binary sums by default; 
     all others are declared on demand *)
  let _ = ignore (sumid 0); ignore (sumid 2)

  let param_count id = List.length (String.Table.find_exn datatypes id).params

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
    List.map ~f:(fun a -> subst a param_subst) ts

  let is_discriminated id =
    (String.Table.find_exn datatypes id).discriminated

  let is_recursive id =
    let rec check_rec a =
      match case a with
      | Var -> false
      | Sgn s ->
        begin
          match s with
          | ZeroB | UnitB | IntB -> false
          | EncodedB(b1) | BoxB(b1) -> check_rec b1
          | ArrayB(b1) -> check_rec b1
          | PairB(b1, b2) -> check_rec b1 && check_rec b2
          | DataB(id', bs) -> id = id' || List.exists ~f:check_rec bs
        end
    in
    let freshparams = List.init (param_count id) ~f:(fun _ -> newvar ()) in
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

  let make name ~param_count:nparams ~discriminated:discriminated =
    String.Table.replace datatypes ~key:name
      ~data:{ name = name;
              (* (these type variables must remain private) *)
              params = List.init nparams ~f:(fun _ -> newvar ());
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
      match case a with
      | Var -> ()
      | Sgn s ->
        begin
          match s with
          | EncodedB _ | IntB | UnitB | ZeroB -> ()
          | PairB(a1, a2) ->
            check_rec_occ a1;
            check_rec_occ a2
          | DataB(id', params) ->
            if (id = id') then
              failwith "Recursive occurrences are only allowed within box<...>"
            else
              List.iter params ~f:check_rec_occ
          | BoxB _ -> ()
          | ArrayB _ -> ()
        end
    in
    check_rec_occ argtype;

    (* replace given parameters by private parameters *)
    let param_subst alpha =
      let l = List.zip_exn paramvars d.params in
      List.Assoc.find l alpha
      |> Option.value ~default:alpha in
    let argtype' = subst argtype param_subst in
    let d' = { d with constructors = d.constructors @ [name, argtype'] } in
    String.Table.replace datatypes ~key:id ~data:d'
end
