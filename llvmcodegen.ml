open Core.Std

let context = Llvm.global_context ()
let builder = Llvm.builder context

(** The type used to represent [int] values and pointers. 
    The code currently uses the assumption that machine pointers
    can be represented as [int] values. This should be changed.*)    
let native_int = Llvm.i64_type context

(** Position builder at start of block *)
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
  Llvm.position_builder block_begin builder

(** Number of bits needed to store [i] different values. *)
let rec log i =
  if i > 1 then 1 + (log (i - i/2)) else 0

module M = Int.Map

(** A profile is a finite map from bit widths to numbers.
    We use vectors of values of varying bit widths below.
    The profile of a vector explains how many values of
    each bit width it contains.

    Invariant: Profiles are maps whose keys are all > 0 and
    that only map to values > 0.
*)
type profile = int M.t

let merge_profiles (p1: profile) (p2: profile) ~f:(f:int -> int -> int)
  : profile =
  M.merge p1 p2
    ~f:(fun ~key:_ -> function
      | `Both(m, n) -> Some (f m n)
      | `Left(n) | `Right(n) -> Some n)

let add_profiles = merge_profiles ~f:(+)
let max_profiles = merge_profiles ~f:(max)

(*
let print_profile p=
  M.iter p ~f:(fun ~key:i ~data:n -> Printf.printf "%i->%i, " i n);
  Printf.printf "\n"
*)

let singleton_profile i = M.singleton i 1

(* Encapsulate bit vectors to make it easy to change the llvm-encoding. *)
module Mixedvector :
sig
  type t

  (** Profile of vector *)
  val to_profile : t -> profile

  (** Empty vector *)
  val null : t

  (** Singleton vector containing a single value of
      given bit width. The call [singleton n v] produces
      a vector with profile [n -> 1]. *)
  val singleton : int -> Llvm.llvalue -> t

  (** Join two vectors. For each bit width, the vectors are concatenated in
      order. *)
  val concatenate : t -> t -> t

  (** Takes the prefix vector specified by profile and returns also the rest. *)
  val takedrop : t -> profile -> t * t

  (** Take prefix or fill up with undefs so that value fits the profile. *)
  val coerce : t -> profile -> t

  (** Extract the value from a singleton vector. *)
  val llvalue_of_singleton : t -> Llvm.llvalue

  (** Build a vector of singleton phi nodes for the llvalues
      stored in the given vector. *)
  val build_phi:  t * Llvm.llbasicblock -> Llvm.llbuilder -> t

  (** Add an incoming vector to vector of phi nodes. *)
  val add_incoming: t * Llvm.llbasicblock -> t -> unit

  (** Returns an LLVM type that can store a vector of the given profile. *)
  val packing_type: profile -> Llvm.lltype

  (** Encodes a vector into its packing type. *)
  val pack : t -> Llvm.llvalue

  (** Decodes a vector from its packing type. *)
  val unpack : profile -> Llvm.llvalue -> t
end =
struct

  type t = { bits : (Llvm.llvalue list) M.t }

  let null = { bits = M.empty }
  let singleton i v = { bits = M.singleton i [v] }

  let concatenate v w =
    { bits =
        M.merge v.bits w.bits
          ~f:(fun ~key:_ -> function
            | `Both(vn, wn) -> Some (vn @ wn)
            | `Left(vn) | `Right(vn) -> Some vn)
    }

  (* precond: v enthält mindestens so viele Werte, wie vom Profil angegeben *)
  let takedrop v profile =
    { bits = M.mapi profile
               ~f:(fun ~key:n ~data:ln ->
                 let vn = M.find v.bits n
                          |> Option.value ~default:[] in
                 assert (ln <= List.length vn);
                 let vn1, _ = List.split_n vn ln in
                 vn1) },
    { bits = M.fold v.bits
               ~f:(fun ~key:n ~data:vn v2 ->
                 let ln = M.find profile n
                          |> Option.value ~default:0 in
                 let _, vn2 = List.split_n vn ln in
                 if (vn2 <> []) then
                   M.add v2 ~key:n ~data:vn2
                 else v2)
               ~init:M.empty}


  let coerce v profile =
    let rec fill_cut i l n =
      if n = 0 then [] else
        match l with
        | [] ->
          Llvm.undef (Llvm.integer_type context i) :: (fill_cut i [] (n-1))
        | x::xs -> x :: (fill_cut i xs (n-1)) in
    { bits = M.mapi profile
               ~f:(fun ~key:i ~data:n ->
                 let vi = M.find v.bits i
                          |> Option.value ~default:[] in
                 fill_cut i vi n)}

  let llvalue_of_singleton v =
    List.hd_exn (snd (M.min_elt_exn v.bits))

  let to_profile (x: t) : profile =
    M.fold x.bits
      ~f:(fun ~key:n ~data:xs m -> M.add m ~key:n ~data:(List.length xs))
      ~init:M.empty

  let build_phi (x, srcblock) builder =
    let phis bits
      = List.map bits
          ~f:(fun x -> Llvm.build_phi [(x, srcblock)] "x" builder) in
    { bits = M.map x.bits ~f:(fun bits -> phis bits) }

  let add_incoming (y, blocky) x =
    let add_incoming_n (y, blocky) x =
      List.iter2_exn y x
        ~f:(fun yi xi -> Llvm.add_incoming (yi, blocky) xi) in
    List.iter (M.keys y.bits)
      ~f:(fun n -> add_incoming_n
                     (M.find_exn y.bits n, blocky)
                     (M.find_exn x.bits n))

  let packing_type profile =
    let struct_members =
      M.fold profile (* ascending order is guaranteed *)
        ~f:(fun ~key:i ~data:n args ->
          args @ (List.init n ~f:(fun _ -> Llvm.integer_type context i)))
        ~init:[] in
    Llvm.packed_struct_type context (Array.of_list struct_members)

  let pack x =
    let struct_type = to_profile x |> packing_type in
    M.fold x.bits ~f:(fun ~key:_ ~data:xs vals -> vals @ xs) ~init:[]
    |> List.foldi
         ~f:(fun i s v -> Llvm.build_insertvalue s v i "pack" builder)
         ~init: (Llvm.undef struct_type)

  let unpack profile v =
    let bits, _ =
      M.fold profile
        ~f:(fun ~key:k ~data:n (bits, pos)->
          let bitsn =
            List.init n
              ~f:(fun i -> Llvm.build_extractvalue v (pos + i)
                             "unpack" builder) in
          M.add bits ~key:k ~data:bitsn,
          pos + n)
        ~init:(M.empty, 0)
    in {bits = bits}
end

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Mixedvector.t
}

(** To each [a: Basetype.t] we assign a number [payload_size a]
    and a profile [attrib_size a]. 
    The values of type [a] will be represented by
    a list of [(payload_size a)] native int values and 
    a vector with profile [(attrib_size a)].

    TODO: The payload could become part of the profile. Originally,
    the profile was just a bitvector, which was the reason for the
    separation.
*)

let payload_size (a: Basetype.t) : int =
  let rec p_s a =
    let open Basetype in
    match finddesc a with
    | Link _ -> assert false
    | EncodedB -> assert false
    | ZeroB | UnitB -> 0
    | Var -> 0
    | IntB -> 1
    | BoxB _ -> 1
    | ArrayB _ -> 1
    | PairB(a1, a2) -> p_s a1 + (p_s a2)
    | DataB(id, ps) ->
      let cs = Basetype.Data.constructor_types id ps in
      List.fold_right cs ~f:(fun c m -> max (p_s c) m) ~init:0
  in p_s a

let attrib_size (a: Basetype.t) : profile =
  let rec a_s a =
    let open Basetype in
    match finddesc a with
    | Link _ -> assert false
    | EncodedB -> assert false
    | Var | ZeroB | UnitB | IntB | BoxB _ | ArrayB _ -> M.empty
    | PairB(a1, a2) -> add_profiles (a_s a1) (a_s a2)
    | DataB(id, ps) ->
      begin
        let cs = Basetype.Data.constructor_types id ps in
        let n = List.length cs in
        let mx = List.fold_right cs ~f:(fun c mx -> max_profiles (a_s c) mx)
                   ~init:M.empty in
        if n = 1 || Basetype.Data.is_discriminated id = false then
          mx
        else
          let i = log n in
          let ni = M.find mx i |> Option.value ~default:0 in
          M.add mx ~key:i ~data:(ni + 1)
      end
  in a_s a

(** Assertion to state tenc encodes a value of type a. *)
let assert_type tenc a =
  assert (List.length tenc.payload = payload_size a);
  assert (M.equal (=) (attrib_size a)
            (Mixedvector.to_profile tenc.attrib))

(** Truncate or fill with undefs the vectors in [enc], so
    that it becomes a value of type [a]. *)
let build_truncate_extend (enc : encoded_value) (a : Basetype.t)
  : encoded_value =
  let a_payload_size = payload_size a in
  let a_attrib_bitlen = attrib_size a in
  let rec mk_payload p n =
    if n = 0 then [] else
      match p with
      | [] -> Llvm.undef (native_int) :: (mk_payload [] (n-1))
      | x::xs -> x :: (mk_payload xs (n-1)) in
  let x_payload = mk_payload enc.payload a_payload_size in
  let x_attrib = Mixedvector.coerce enc.attrib a_attrib_bitlen in
  { payload = x_payload; attrib = x_attrib }

let packing_type (a: Basetype.t) : Llvm.lltype =
  let len_p = payload_size a in
  let struct_members =
    Array.append
      (Array.create ~len:len_p native_int)
      (Array.create ~len:1 (Mixedvector.packing_type (attrib_size a))) in
  let struct_type = Llvm.packed_struct_type context struct_members in
  struct_type

let pack_encoded_value (enc: encoded_value) (a: Basetype.t): Llvm.llvalue =
  assert_type enc a;
  let struct_type = packing_type a in
  let packed_enc =
    List.foldi (enc.payload @ [Mixedvector.pack enc.attrib])
      ~f:(fun i s v -> Llvm.build_insertvalue s v i "packed" builder)
      ~init:(Llvm.undef struct_type) in
  packed_enc

let unpack_encoded_value (packed_enc: Llvm.llvalue) (a: Basetype.t)
  : encoded_value =
  let len_p = payload_size a in
  let len_a = attrib_size a in
  let pl = List.init len_p
             ~f:(fun i -> Llvm.build_extractvalue packed_enc i "p" builder) in
  let at = Llvm.build_extractvalue packed_enc len_p "a" builder in
  {payload = pl; attrib = Mixedvector.unpack len_a at}

(** Encoding of values *)
let rec build_value
      (the_module : Llvm.llmodule)
      (ctx: (Ident.t * encoded_value) list)
      (t: Ssa.value) : encoded_value =
  match t with
  | Ssa.Var(x) ->
    List.Assoc.find_exn ctx x
  | Ssa.IntConst(i) ->
    let vali = Llvm.const_int (native_int) i in
    {payload = [vali]; attrib = Mixedvector.null;}
  | Ssa.Unit ->
    {payload = []; attrib = Mixedvector.null}
  | Ssa.Pair(t1, t2) ->
    let t1enc = build_value the_module ctx t1 in
    let t2enc = build_value the_module ctx t2 in
    let ta = Mixedvector.concatenate t1enc.attrib t2enc.attrib in
    {payload = t1enc.payload @ t2enc.payload; attrib = ta}
  | Ssa.In((id, _, t), a) when
      Basetype.Data.constructor_count id = 1 ||
      Basetype.Data.is_discriminated id = false ->
    let tenc = build_value the_module ctx t in
    build_truncate_extend tenc a
  | Ssa.In((id, i, t), a) ->
    let n = Basetype.Data.constructor_count id in
    let tenc = build_value the_module ctx t in
    let branch = Llvm.const_int (Llvm.integer_type context (log n)) i in
    let attrib_branch = Mixedvector.concatenate (Mixedvector.singleton (log n) branch)
                          tenc.attrib in
    let denc = { payload = tenc.payload; attrib = attrib_branch} in
    build_truncate_extend denc a
  | Ssa.Fst(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_ap = payload_size a in
    let len_bp = payload_size b in
    let len_aa = attrib_size a in
    assert (List.length tenc.payload = len_ap + len_bp);
    let t1p, _ = List.split_n tenc.payload len_ap in
    let t1a, t2a = Mixedvector.takedrop tenc.attrib len_aa in
    assert (M.equal (=) (attrib_size a) (Mixedvector.to_profile t1a));
    assert (M.equal (=) (attrib_size b) (Mixedvector.to_profile t2a));
    {payload = t1p; attrib = t1a }
  | Ssa.Snd(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_ap = payload_size a in
    let len_bp = payload_size b in
    let len_aa = attrib_size a in
    assert (List.length tenc.payload = len_ap + len_bp);
    let _ , t2p = List.split_n tenc.payload len_ap in
    let t1a, t2a = Mixedvector.takedrop tenc.attrib len_aa in
    assert (M.equal (=) (attrib_size a) (Mixedvector.to_profile t1a));
    assert (M.equal (=) (attrib_size b) (Mixedvector.to_profile t2a));
    {payload = t2p; attrib = t2a }
  | Ssa.Select(t, (id, params), i)
    when Basetype.Data.is_discriminated id = false ->
    let tenc = build_value the_module ctx t in
    let case_types = Basetype.Data.constructor_types id params in
    let ai = List.nth_exn case_types i in
    build_truncate_extend tenc ai
  | Ssa.Select(t, (id, params), i) ->
    let n = Basetype.Data.constructor_count id in
    let tenc = build_value the_module ctx t in
    if n = 1 then
      build_value the_module ctx t
    else
      begin
        let yenc =
          let _, ya =
            Mixedvector.takedrop tenc.attrib (singleton_profile (log n)) in
          {payload = tenc.payload; attrib = ya} in
        let case_types = Basetype.Data.constructor_types id params in
        assert (i < List.length case_types);
        let ai = List.nth_exn case_types i in
        build_truncate_extend yenc ai
      end
  | Ssa.Undef(a) ->
    build_truncate_extend {payload = []; attrib = Mixedvector.null} a

let build_term
      (the_module : Llvm.llmodule)
      (ctx: (Ident.t * encoded_value) list)
      (t: Ssa.term) : encoded_value =
  match t with
  | Ssa.Val(v) -> build_value the_module ctx v
  | Ssa.Const(Ast.Cpush(a), v) ->
    let salloctype = Llvm.function_type
                       (Llvm.pointer_type (Llvm.i8_type context))
                       (Array.of_list [native_int]) in
    let salloc = Llvm.declare_function "salloc" salloctype the_module in
    let a_struct = packing_type a in
    let mem_i8ptr = Llvm.build_call salloc
                      (Array.of_list [Llvm.size_of a_struct])
                      "memi8" builder in
    let mem_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct)
                    "memstruct" builder in
    let venc = build_value the_module ctx v in
    let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
    ignore (Llvm.build_store v_packed mem_ptr builder);
    {payload = []; attrib = Mixedvector.null}
  | Ssa.Const(Ast.Cpop(a), _) ->
    let spoptype = Llvm.function_type
                     (Llvm.pointer_type (Llvm.i8_type context))
                     (Array.of_list [native_int]) in
    let spop = Llvm.declare_function "spop" spoptype the_module in
    let a_struct = packing_type a in
    let mem_i8ptr = Llvm.build_call spop (Array.of_list [Llvm.size_of a_struct])
                      "memi8" builder in
    let mem_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct)
                    "memstruct" builder in
    let lstruct = Llvm.build_load mem_ptr "lstruct" builder in
    unpack_encoded_value lstruct a
  | Ssa.Const(Ast.Cprint(s), _) ->
    let str = Llvm.build_global_string s "s" builder in
    let strptr = Llvm.build_in_bounds_gep str
                   (Array.create ~len:2 (Llvm.const_null native_int)) "strptr" builder in
    let strptrint = Llvm.build_ptrtoint strptr native_int "strptrint" builder in
    let i8a = Llvm.pointer_type (Llvm.i8_type context) in
    let formatstr = Llvm.build_global_string "%s" "format" builder in
    let formatstrptr = Llvm.build_in_bounds_gep formatstr
                         (Array.create ~len:2 (Llvm.const_null native_int))
                         "forrmatptr" builder in
    let printftype = Llvm.function_type (native_int)
                       (Array.of_list [i8a; native_int]) in
    let printf = Llvm.declare_function "printf" printftype the_module in
    let args = Array.of_list [formatstrptr; strptrint] in
    ignore (Llvm.build_call printf args "i" builder);
    {payload = []; attrib = Mixedvector.null}
  | Ssa.Const(Ast.Ccall(e, a, b), v) ->
    let a_struct = packing_type a in
    let b_struct = packing_type b in
    let etype = Llvm.function_type b_struct (Array.of_list [a_struct]) in
    let efunc = Llvm.declare_function e etype the_module in
    let venc = build_value the_module ctx v in
    let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
    let args = Array.of_list [v_packed] in
    let res_packed = Llvm.build_call efunc args e builder in
    unpack_encoded_value res_packed b
  | Ssa.Const(Ast.Cintadd as const, arg)
  | Ssa.Const(Ast.Cintsub as const, arg)
  | Ssa.Const(Ast.Cintmul as const, arg)
  | Ssa.Const(Ast.Cintdiv as const, arg)
  | Ssa.Const(Ast.Cinteq as const, arg)
  | Ssa.Const(Ast.Cintlt as const, arg)
  | Ssa.Const(Ast.Cintslt as const, arg)
  | Ssa.Const(Ast.Cintshl as const, arg)
  | Ssa.Const(Ast.Cintshr as const, arg)
  | Ssa.Const(Ast.Cintsar as const, arg)
  | Ssa.Const(Ast.Cintand as const, arg)
  | Ssa.Const(Ast.Cintor as const, arg)
  | Ssa.Const(Ast.Cintxor as const, arg)
  | Ssa.Const(Ast.Cintprint as const, arg)
  | Ssa.Const(Ast.Calloc _ as const, arg)
  | Ssa.Const(Ast.Cfree _ as const, arg)
  | Ssa.Const(Ast.Cload _ as const, arg)
  | Ssa.Const(Ast.Cstore _ as const, arg) 
  | Ssa.Const(Ast.Carrayalloc _ as const, arg)
  | Ssa.Const(Ast.Carrayfree _ as const, arg)
  | Ssa.Const(Ast.Carrayget _ as const, arg) ->
    begin
      let argenc = build_value the_module ctx arg in
      match const, argenc.payload with
      | Ast.Cintadd, [x; y] ->
        {payload = [Llvm.build_add x y "add" builder];
         attrib = Mixedvector.null}
      | Ast.Cintadd, _ -> failwith "internal: wrong argument to intadd"
      | Ast.Cintsub, [x; y] ->
        {payload = [Llvm.build_sub x y "sub" builder];
         attrib = Mixedvector.null}
      | Ast.Cintsub, _ -> failwith "internal: wrong argument to intsub"
      | Ast.Cintmul, [x; y] ->
        {payload = [Llvm.build_mul x y "mul" builder];
         attrib = Mixedvector.null}
      | Ast.Cintmul, _ -> failwith "internal: wrong argument to intmul"
      | Ast.Cintdiv, [x; y] ->
        {payload = [Llvm.build_sdiv x y "sdiv" builder];
         attrib = Mixedvector.null}
      | Ast.Cintdiv, _ -> failwith "internal: wrong argument to intdiv"
      | Ast.Cinteq, [x; y] ->
        {payload = [];
         attrib = Mixedvector.singleton 1
                    (Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder)}
      | Ast.Cinteq, _ -> failwith "internal: wrong argument to inteq"
      | Ast.Cintlt, [x; y] ->
        {payload = [];
         attrib = Mixedvector.singleton 1
                    (Llvm.build_icmp Llvm.Icmp.Uge x y "lt" builder )}
      | Ast.Cintlt, _ -> failwith "internal: wrong argument to intslt"
      | Ast.Cintslt, [x; y] ->
        {payload = [];
         attrib = Mixedvector.singleton 1
                    (Llvm.build_icmp Llvm.Icmp.Sge x y "slt" builder )}
      | Ast.Cintslt, _ -> failwith "internal: wrong argument to intslt"
      | Ast.Cintshl, [x; y] ->
        {payload = [Llvm.build_shl x y "shl" builder];
         attrib = Mixedvector.null}
      | Ast.Cintshl, _ -> failwith "internal: wrong argument to intshl"
      | Ast.Cintshr, [x; y] ->
        {payload = [Llvm.build_lshr x y "shr" builder ];
         attrib = Mixedvector.null}
      | Ast.Cintshr, _ -> failwith "internal: wrong argument to intshr"
      | Ast.Cintsar, [x; y] ->
        {payload = [Llvm.build_ashr x y "sar" builder ];
         attrib = Mixedvector.null}
      | Ast.Cintsar, _ -> failwith "internal: wrong argument to intsar"
      | Ast.Cintand, [x; y] ->
        {payload = [Llvm.build_and x y "and" builder ];
         attrib = Mixedvector.null}
      | Ast.Cintand, _ -> failwith "internal: wrong argument to intand"
      | Ast.Cintor, [x; y] ->
        {payload = [Llvm.build_or x y "or" builder ];
         attrib = Mixedvector.null}
      | Ast.Cintor, _ -> failwith "internal: wrong argument to intor"
      | Ast.Cintxor, [x; y] ->
        {payload = [Llvm.build_xor x y "xor" builder ];
         attrib = Mixedvector.null}
      | Ast.Cintxor, _ -> failwith "internal: wrong argument to intxor"
      | Ast.Cintprint, [x] ->
        let i8a = Llvm.pointer_type (Llvm.i8_type context) in
        let formatstr = Llvm.build_global_string "%i" "format" builder in
        let formatstrptr = Llvm.build_in_bounds_gep formatstr
                             (Array.create ~len:2 (Llvm.const_null native_int))
                             "forrmatptr" builder in
        let printftype = Llvm.function_type (native_int)
                           (Array.of_list [i8a; native_int]) in
        let printf = Llvm.declare_function "printf" printftype the_module in
        let args = Array.of_list [formatstrptr; x] in
        ignore (Llvm.build_call printf args "i" builder);
        {payload = []; attrib = Mixedvector.null }
      | Ast.Cintprint, _ -> failwith "internal: wrong argument to intprint"
      | Ast.Calloc(a), _ ->
        let malloc =
          match Llvm.lookup_function "malloc" the_module with
          | Some malloc -> malloc
          | None -> assert false in
        let a_struct = packing_type a in
        let mem_i8ptr = Llvm.build_call malloc
                          (Array.of_list [Llvm.size_of a_struct])
                          "memi8" builder in
        let addr = Llvm.build_ptrtoint mem_i8ptr native_int "memint" builder in
        {payload = [addr]; attrib = Mixedvector.null}
      | Ast.Cfree _, [addr] ->
        let free =
          match Llvm.lookup_function "free" the_module with
          | Some free -> free
          | None -> assert false in
        ignore (Llvm.build_call free (Array.of_list [addr]) "free" builder);
        {payload = []; attrib = Mixedvector.null}
      | Ast.Cfree _, _ -> failwith "internal: wrong argument to free"
      | Ast.Cload a, [addr] ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_inttoptr addr
                        (Llvm.pointer_type a_struct) "memptr" builder in
        let lstruct = Llvm.build_load mem_ptr "lstruct" builder in
        unpack_encoded_value lstruct a
      | Ast.Cload _, _ -> failwith "internal: wrong argument to load"
      | Ast.Cstore a, (addr :: vpayload)  ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_inttoptr addr
                        (Llvm.pointer_type a_struct) "memptr" builder in
        (* The following depends on the encoding of box and pairs and
         * is probably fragile! *)
        let venc = { payload = vpayload; attrib = argenc.attrib } in
        let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
        ignore (Llvm.build_store v_packed mem_ptr builder);
        {payload = []; attrib = Mixedvector.null}
      | Ast.Cstore _, _ -> failwith "internal: wrong argument to store"
      | Ast.Carrayalloc a, [length] ->
        let a_struct = packing_type a in
        let malloc =
          match Llvm.lookup_function "malloc" the_module with
          | Some malloc -> malloc
          | None -> assert false in
        let byte_size =
          Llvm.build_mul length (Llvm.size_of a_struct) "size" builder in
        let mem_i8ptr = Llvm.build_call malloc
                          (Array.of_list [byte_size])
                          "memi8" builder in
        let addr = Llvm.build_ptrtoint mem_i8ptr native_int "memint" builder in
        {payload = [addr]; attrib = Mixedvector.null}
      | Ast.Carrayalloc _, _ -> failwith "internal: wrong argument to arrayalloc"
      | Ast.Carrayfree _, [addr] ->
        let free =
          match Llvm.lookup_function "free" the_module with
          | Some free -> free
          | None -> assert false in
        ignore (Llvm.build_call free (Array.of_list [addr]) "free" builder);
        {payload = []; attrib = Mixedvector.null}
      | Ast.Carrayfree _, _ -> failwith "internal: wrong argument to arrayfree"
      | Ast.Carrayget a, [addr; idx] ->
        let a_struct = packing_type a in
        let offset =
          let p1 = Llvm.build_mul idx (Llvm.size_of a_struct) "p1" builder in
          Llvm.build_add addr p1 "offset" builder in
        {payload = [offset]; attrib = Mixedvector.null}
      | Ast.Carrayget _, _ -> failwith "internal: wrong argument to arrayget"
      | Ast.Cprint _, _
      | Ast.Cpush _, _
      | Ast.Cpop _, _
      | Ast.Ccall _, _
      | Ast.Cencode _, _
      | Ast.Cdecode _, _
        -> assert false
    end
  | Ssa.Const(Ast.Cencode _, _)
  | Ssa.Const(Ast.Cdecode _, _) ->
    assert false

let rec build_letbindings
      (the_module : Llvm.llmodule)
          (ctx: (Ident.t * encoded_value) list)
          (l: Ssa.let_bindings)
  : (Ident.t * encoded_value) list =
  match l with
  | [] -> ctx
  | Ssa.Let((x, a), t) :: lets ->
    let ctx1 = build_letbindings the_module ctx lets in
    let tenc = build_term the_module ctx1 t in
    assert_type tenc a;
    (x, tenc) :: ctx1

let build_body
      (the_module : Llvm.llmodule)
      (ctx: (Ident.t * encoded_value) list)
      (l: Ssa.let_bindings)
      (v: Ssa.value)
  : encoded_value =
  let ctx1 = build_letbindings the_module ctx l in
  build_value the_module ctx1 v

let build_ssa_blocks (the_module : Llvm.llmodule) (func : Llvm.llvalue)
      (ssa_func : Ssa.t) : unit =
  let label_types = Int.Table.create () in
  List.iter ssa_func.Ssa.blocks
    ~f:(fun b ->
      let l = Ssa.label_of_block b in
      Int.Table.replace label_types ~key:l.Ssa.name ~data:l.Ssa.message_type);

  let blocks = Int.Table.create () in
  let phi_nodes = Int.Table.create () in
  let get_block name =
    match Int.Table.find blocks name with
    | Some block -> block
    | None ->
      let label = Printf.sprintf "L%i" name in
      let block = Llvm.append_block context label func in
      Int.Table.replace blocks ~key:name ~data:block;
      block in
  let connect_to src_block encoded_value dst =
    try
      assert_type encoded_value (Int.Table.find_exn label_types dst);
      let phi = Int.Table.find_exn phi_nodes dst in
      List.iter2_exn phi.payload encoded_value.payload
        ~f:(fun phix  x -> Llvm.add_incoming (x, src_block) phix);
      Mixedvector.add_incoming (encoded_value.attrib, src_block) phi.attrib
    (* add (encoded_value, source) to phi node *)
    with Not_found ->
      (* TODO: Bei Grad 1 braucht man keine Phi-Knoten *)
      begin
        position_at_start (get_block dst) builder;
        let payload =
          List.map encoded_value.payload
            ~f: (fun x -> Llvm.build_phi [(x, src_block)] "g" builder) in
        let attrib = Mixedvector.build_phi
                       (encoded_value.attrib, src_block) builder in
        let phi = { payload = payload; attrib = attrib } in
        Int.Table.replace phi_nodes ~key:dst ~data:phi
      end
  in
  (* make entry block *)
  let entry_block = Llvm.append_block context "entry" func in
  let packed_arg = Llvm.param func 0 in
  Llvm.set_value_name "packed_arg" packed_arg;
  Llvm.position_at_end entry_block builder;
  let arg = unpack_encoded_value packed_arg
              ssa_func.Ssa.entry_label.Ssa.message_type in
  ignore (Llvm.build_br (get_block ssa_func.Ssa.entry_label.Ssa.name) builder);
  connect_to entry_block arg ssa_func.Ssa.entry_label.Ssa.name;
  (* build unconnected blocks *)
  let open Ssa in
  List.iter ssa_func.blocks
    ~f:(fun block ->
      flush stdout;
      match block with
      | Unreachable(src) ->
        Llvm.position_at_end (get_block src.name) builder;
        ignore (Llvm.build_unreachable builder)
      | Direct(src, x, lets, body, dst) ->
        Llvm.position_at_end (get_block src.name) builder;
        let senc = Int.Table.find_exn phi_nodes src.name in
        assert_type senc src.message_type;
        let ev = build_body the_module [(x, senc)] lets body in
        let src_block = Llvm.insertion_block builder in
        ignore (Llvm.build_br (get_block dst.name) builder);
        connect_to src_block ev dst.name
      | Branch(src, x, lets, (id, params, body, cases)) ->
        begin
          Llvm.position_at_end (get_block src.name) builder;
          let xenc = Int.Table.find_exn phi_nodes src.name in
          assert_type xenc src.message_type;
          let ctx = build_letbindings the_module [(x, xenc)] lets in
          let ebody = build_value the_module ctx body in
          let n = List.length cases in
          assert (n > 0);
          match cases with
          | [(y, v, dst)] ->
            let venc =
              build_value the_module ((y, ebody)::ctx) v in
            let this_block = Llvm.insertion_block builder in
            ignore (Llvm.build_br (get_block dst.name) builder);
            connect_to this_block venc dst.name
          | _ ->
            let cond, yenc =
              let ienc, ya =
                Mixedvector.takedrop ebody.attrib (singleton_profile (log n)) in
              let cond = Mixedvector.llvalue_of_singleton ienc in
              cond, {payload = ebody.payload; attrib = ya } in
            let case_types = Basetype.Data.constructor_types id params in
            let jump_targets =
              List.map2_exn cases case_types
                ~f:(fun (y, v, dst) a ->
                  (y, build_truncate_extend yenc a), v, dst) in
            let func = Llvm.block_parent (Llvm.insertion_block builder) in
            let case_blocks =
              List.init n
                ~f:(fun i -> Llvm.append_block context
                               ("case" ^ (string_of_int i)) func) in
            let default_block = List.hd_exn case_blocks in
            let switch =
              Llvm.build_switch cond default_block (n-1) builder in
            (* build case blocks *)
            List.iteri (List.zip_exn case_blocks jump_targets)
              ~f:(fun i (block, ((y, yenc), v, dst)) ->
                 if i > 0 then
                   Llvm.add_case switch
                     (Llvm.const_int (Llvm.integer_type context (log n)) i)
                     block;
                 Llvm.position_at_end block builder;
                 let venc = build_value the_module ((y, yenc)::ctx) v in
                 let this_block = Llvm.insertion_block builder in
                 ignore (Llvm.build_br (get_block dst.name) builder);
                 connect_to this_block venc dst.name
              )
        end
      | Return(src, x, lets, body, return_type) ->
        Llvm.position_at_end (get_block src.name) builder;
        let xenc = Int.Table.find_exn phi_nodes src.name in
        let ev = build_body the_module [(x, xenc)] lets body in
        let pev = pack_encoded_value ev return_type in
        ignore (Llvm.build_ret pev builder)
    )

let llvm_compile (ssa_func : Ssa.t) : Llvm.llmodule =
  let the_module = Llvm.create_module context "int" in

  (* General function declarations *)
  let malloctype = Llvm.function_type
                     (Llvm.pointer_type (Llvm.i8_type context))
                     (Array.of_list [native_int]) in
  ignore (Llvm.declare_function "malloc" malloctype the_module);
  let freetype = Llvm.function_type
                   (Llvm.pointer_type (Llvm.i8_type context))
                   (Array.of_list [native_int]) in
  ignore (Llvm.declare_function "free" freetype the_module);

  (* Main function *)
  let arg_ty = packing_type ssa_func.Ssa.entry_label.Ssa.message_type in
  let ret_ty = packing_type ssa_func.Ssa.return_type in
  let ft = Llvm.function_type ret_ty (Array.create ~len:1 arg_ty) in
  let func = Llvm.declare_function
               ("Int" ^ ssa_func.Ssa.func_name) ft the_module in
  build_ssa_blocks the_module func ssa_func;
  (* make main function *)
  if ssa_func.Ssa.func_name = "main" then
    begin
      let void_ty = Llvm.void_type context in
      let main_ty = Llvm.function_type native_int (Array.create ~len:0 void_ty) in
      let main = Llvm.declare_function "main" main_ty the_module in
      let start_block = Llvm.append_block context "start" main in
      let args = Array.of_list [Llvm.undef arg_ty] in
      Llvm.position_at_end start_block builder;
      ignore (Llvm.build_call func args "ret" builder);
      ignore (Llvm.build_ret (Llvm.const_int native_int 0) builder)
    end;
  (* Llvm.dump_module the_module; *)
  the_module

