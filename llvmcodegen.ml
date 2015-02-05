open Core.Std

let context = Llvm.global_context ()
let builder = Llvm.builder context

(** The type used to represent [int] values and pointers.
    The code currently uses the assumption that machine pointers
    can be represented as [int] values. This should be changed.*)
let int_size = 64
let native_int = Llvm.i64_type context

(** Position builder at start of block *)
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
  Llvm.position_builder block_begin builder

(** Number of bits needed to store [i] different values. *)
let rec log i =
  if i > 1 then 1 + (log (i - i/2)) else 0

(** A profile is a finite map from bit widths to numbers.
    We use vectors of values of varying bit widths below.
    The profile of a vector explains how many values of
    each bit width it contains.

    The following module enforces the invariant that
    keys are all > 0 and if a key has a value then this
    value is > 0.
*)
module Profile: sig
  module Key = Int
  type t

  val null : t
  val singleton : Key.t -> t
  val ntimes : Key.t -> int -> t
  val add : t -> t -> t

  val of_basetype: Basetype.t -> t

  val equal : t -> t -> bool
  val find : t -> Key.t -> int option
  val mapi : t -> f:(key:Key.t -> data:int -> 'a) -> 'a Key.Map.t
  val fold_right : t -> init:'a -> f:(key:Key.t -> data:int -> 'a -> 'a) -> 'a

end
= struct
  module Key = Int
  type t = int Key.Map.t

  let null = Key.Map.empty
  let singleton i = Key.Map.singleton i 1
  let ntimes i n =
    if n <=0 then failwith "ntimes argument";
    Key.Map.singleton i n

  let merge (p1: t) (p2: t) ~f:(f:int -> int -> int) : t =
    Key.Map.merge p1 p2
      ~f:(fun ~key:_ -> function
        | `Both(m, n) -> Some (f m n)
        | `Left(n) | `Right(n) -> Some n)

  let add = merge ~f:(+)
  let max = merge ~f:(max)

  (*
  let print p =
    Key.Map.iter p ~f:(fun ~key:i ~data:n -> Printf.printf "%i->%i, " i n);
    Printf.printf "\n"
  *)

  let of_basetype (a: Basetype.t) : t =
    let rec a_s a =
      let open Basetype in
      match case a with
      | Var -> null
      | Sgn sa ->
        begin
          match sa with
          | EncodedB _ -> assert false
          | ZeroB | UnitB -> null
          | IntB | BoxB _ | ArrayB _ -> singleton int_size
          | PairB(a1, a2) -> add (a_s a1) (a_s a2)
          | DataB(id, ps) ->
            begin
              let cs = Basetype.Data.constructor_types id ps in
              let n = List.length cs in
              let mx = List.fold_right cs ~f:(fun c mx -> max (a_s c) mx)
                         ~init:Key.Map.empty in
              if n = 1 || Basetype.Data.is_discriminated id = false then
                mx
              else
                let i = log n in
                let ni = Key.Map.find mx i |> Option.value ~default:0 in
                Key.Map.add mx ~key:i ~data:(ni + 1)
            end
        end
    in a_s a

  let equal = Key.Map.equal (=)
  let find = Key.Map.find
  let mapi = Key.Map.mapi
  let fold_right = Key.Map.fold_right
end

(* Encapsulate vectors of values of varying bit width. *)
module Mixedvector :
sig
  type t

  (** Profile of vector *)
  val to_profile : t -> Profile.t

  (** Empty vector *)
  val null : t

  (** Singleton vector containing a single value of
      given bit width. The call [singleton n v] produces
      a vector with profile [n -> 1]. *)
  val singleton : Profile.Key.t -> Llvm.llvalue -> t

  (** Join two vectors. For each bit width, the vectors are concatenated in
      order. *)
  val concatenate : t -> t -> t

  (** Takes the prefix vector specified by profile and returns also the rest. *)
  val takedrop : t -> Profile.t -> t * t

  (** Take prefix or fill up with undefs so that value fits the profile. *)
  val coerce : t -> Profile.t -> t

  (** Extract the value from a singleton vector. *)
  val llvalue_of_singleton : t -> Llvm.llvalue

  (** Extract the list of all values for a given key. *)
  val llvalues_at_key: t -> Profile.Key.t -> Llvm.llvalue list

  (** Build a vector of singleton phi nodes for the llvalues
      stored in the given vector. *)
  val build_phi:  t * Llvm.llbasicblock -> Llvm.llbuilder -> t

  (** Add an incoming vector to vector of phi nodes. *)
  val add_incoming: t * Llvm.llbasicblock -> t -> unit

  (** Returns an LLVM type that can store a vector of the given profile. *)
  val packing_type: Profile.t -> Llvm.lltype

  (** Encodes a vector into its packing type. *)
  val pack : t -> Llvm.llvalue

  (** Decodes a vector from its packing type. *)
  val unpack : Profile.t -> Llvm.llvalue -> t
end =
struct

  type t = { bits : (Llvm.llvalue list) Int.Map.t }

  let null = { bits = Int.Map.empty }
  let singleton i v = { bits = Int.Map.singleton i [v] }

  let concatenate v w =
    { bits =
        Int.Map.merge v.bits w.bits
          ~f:(fun ~key:_ -> function
            | `Both(vn, wn) -> Some (vn @ wn)
            | `Left(vn) | `Right(vn) -> Some vn)
    }

  (* precond: v enthält mindestens so viele Werte, wie vom Profil angegeben *)
  let takedrop v profile =
    { bits = Profile.mapi profile
               ~f:(fun ~key:n ~data:ln ->
                 let vn = Int.Map.find v.bits n
                          |> Option.value ~default:[] in
                 assert (ln <= List.length vn);
                 let vn1, _ = List.split_n vn ln in
                 vn1) },
    { bits = Int.Map.fold v.bits
               ~f:(fun ~key:n ~data:vn v2 ->
                 let ln = Profile.find profile n
                          |> Option.value ~default:0 in
                 let _, vn2 = List.split_n vn ln in
                 if (vn2 <> []) then
                   Int.Map.add v2 ~key:n ~data:vn2
                 else v2)
               ~init:Int.Map.empty}


  let coerce v profile =
    let rec fill_cut i l n =
      if n = 0 then [] else
        match l with
        | [] ->
          Llvm.undef (Llvm.integer_type context i) :: (fill_cut i [] (n-1))
        | x::xs -> x :: (fill_cut i xs (n-1)) in
    { bits = Profile.mapi profile
               ~f:(fun ~key:i ~data:n ->
                 let vi = Int.Map.find v.bits i
                          |> Option.value ~default:[] in
                 fill_cut i vi n)}

  let llvalue_of_singleton v =
    List.hd_exn (snd (Int.Map.min_elt_exn v.bits))

  let llvalues_at_key (x: t) (k: Profile.Key.t) =
    Int.Map.find x.bits k |> Option.value ~default:[]

  let to_profile (x: t) : Profile.t =
    Int.Map.fold x.bits
      ~f:(fun ~key:k ~data:xs m ->
        Profile.add (Profile.ntimes k (List.length xs)) m)
      ~init:Profile.null

  let build_phi (x, srcblock) builder =
    let phis bits
      = List.map bits
          ~f:(fun x -> Llvm.build_phi [(x, srcblock)] "x" builder) in
    { bits = Int.Map.map x.bits ~f:(fun bits -> phis bits) }

  let add_incoming (y, blocky) x =
    let add_incoming_n (y, blocky) x =
      List.iter2_exn y x
        ~f:(fun yi xi -> Llvm.add_incoming (yi, blocky) xi) in
    List.iter (Int.Map.keys y.bits)
      ~f:(fun n -> add_incoming_n
                     (Int.Map.find_exn y.bits n, blocky)
                     (Int.Map.find_exn x.bits n))

  let packing_type profile =
    let struct_members =
      Profile.fold_right profile (* ascending order is guaranteed *)
        ~f:(fun ~key:i ~data:n args ->
          args @ (List.init n ~f:(fun _ -> Llvm.integer_type context i)))
        ~init:[] in
    Llvm.packed_struct_type context (Array.of_list struct_members)

  let pack x =
    let struct_type = to_profile x |> packing_type in
    Int.Map.fold_right x.bits ~f:(fun ~key:_ ~data:xs vals -> vals @ xs) ~init:[]
    |> List.foldi
         ~f:(fun i s v -> Llvm.build_insertvalue s v i "pack" builder)
         ~init: (Llvm.undef struct_type)

  let unpack profile v =
    let bits, _ =
      Profile.fold_right profile
        ~f:(fun ~key:k ~data:n (bits, pos)->
          let bitsn =
            List.init n
              ~f:(fun i -> Llvm.build_extractvalue v (pos + i)
                             "unpack" builder) in
          Int.Map.add bits ~key:k ~data:bitsn,
          pos + n)
        ~init:(Int.Map.empty, 0)
    in {bits = bits}
end

type encoded_value = Mixedvector.t

(** To each [a: Basetype.t] we assign a profile [Profile.of_basetype a].
    The values of type [a] will be represented by
    a vector with profile [(Profile.of_basetype a)].
*)

(** Assertion to state tenc encodes a value of type a. *)
let assert_type tenc a =
  (*  assert (List.length tenc.payload = payload_size a); *)
  assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile tenc))

(** Truncate or fill with undefs the vectors in [enc], so
    that it becomes a value of type [a]. *)
let build_truncate_extend (enc : encoded_value) (a : Basetype.t)
  : encoded_value =
  (*  let a_payload_size = payload_size a in *)
  let a_attrib_bitlen = Profile.of_basetype a in
  Mixedvector.coerce enc a_attrib_bitlen

let packing_type (a: Basetype.t) : Llvm.lltype =
  Mixedvector.packing_type (Profile.of_basetype a)

let pack_encoded_value (enc: encoded_value) (a: Basetype.t): Llvm.llvalue =
  assert_type enc a;
  Mixedvector.pack enc

let unpack_encoded_value (packed_enc: Llvm.llvalue) (a: Basetype.t)
  : encoded_value =
  let len_a = Profile.of_basetype a in
  Mixedvector.unpack len_a packed_enc

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
    Mixedvector.singleton int_size vali
  | Ssa.Unit ->
    Mixedvector.null
  | Ssa.Pair(t1, t2) ->
    let t1enc = build_value the_module ctx t1 in
    let t2enc = build_value the_module ctx t2 in
    Mixedvector.concatenate t1enc t2enc
  | Ssa.In((id, _, t), a) when
      Basetype.Data.constructor_count id = 1 ||
      Basetype.Data.is_discriminated id = false ->
    let tenc = build_value the_module ctx t in
    build_truncate_extend tenc a
  | Ssa.In((id, i, t), a) ->
    let n = Basetype.Data.constructor_count id in
    let tenc = build_value the_module ctx t in
    let branch = Llvm.const_int (Llvm.integer_type context (log n)) i in
    let denc = Mixedvector.concatenate (Mixedvector.singleton (log n) branch)
                          tenc in
    build_truncate_extend denc a
  | Ssa.Fst(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_aa = Profile.of_basetype a in
    let t1a, t2a = Mixedvector.takedrop tenc len_aa in
    assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile t1a));
    assert (Profile.equal (Profile.of_basetype b) (Mixedvector.to_profile t2a));
    t1a
  | Ssa.Snd(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_aa = Profile.of_basetype a in
    let t1a, t2a = Mixedvector.takedrop tenc len_aa in
    assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile t1a));
    assert (Profile.equal (Profile.of_basetype b) (Mixedvector.to_profile t2a));
    t2a
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
            Mixedvector.takedrop tenc (Profile.singleton (log n)) in
          ya in
        let case_types = Basetype.Data.constructor_types id params in
        assert (i < List.length case_types);
        let ai = List.nth_exn case_types i in
        build_truncate_extend yenc ai
      end
  | Ssa.Undef(a) ->
    build_truncate_extend Mixedvector.null a

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
    Mixedvector.null
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
    Mixedvector.null
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
      let payload = Mixedvector.llvalues_at_key argenc int_size in
      match const, payload with
      | Ast.Cintadd, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_add x y "add" builder)
      | Ast.Cintadd, _ -> failwith "internal: wrong argument to intadd"
      | Ast.Cintsub, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_sub x y "sub" builder)
      | Ast.Cintsub, _ -> failwith "internal: wrong argument to intsub"
      | Ast.Cintmul, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_mul x y "mul" builder)
      | Ast.Cintmul, _ -> failwith "internal: wrong argument to intmul"
      | Ast.Cintdiv, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_sdiv x y "sdiv" builder)
      | Ast.Cintdiv, _ -> failwith "internal: wrong argument to intdiv"
      | Ast.Cinteq, [x; y] ->
         Mixedvector.singleton 1
           (Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder)
      | Ast.Cinteq, _ -> failwith "internal: wrong argument to inteq"
      | Ast.Cintlt, [x; y] ->
         Mixedvector.singleton 1
           (Llvm.build_icmp Llvm.Icmp.Uge x y "lt" builder )
      | Ast.Cintlt, _ -> failwith "internal: wrong argument to intslt"
      | Ast.Cintslt, [x; y] ->
         Mixedvector.singleton 1
           (Llvm.build_icmp Llvm.Icmp.Sge x y "slt" builder )
      | Ast.Cintslt, _ -> failwith "internal: wrong argument to intslt"
      | Ast.Cintshl, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_shl x y "shl" builder)
      | Ast.Cintshl, _ -> failwith "internal: wrong argument to intshl"
      | Ast.Cintshr, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_lshr x y "shr" builder)
      | Ast.Cintshr, _ -> failwith "internal: wrong argument to intshr"
      | Ast.Cintsar, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_ashr x y "sar" builder)
      | Ast.Cintsar, _ -> failwith "internal: wrong argument to intsar"
      | Ast.Cintand, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_and x y "and" builder)
      | Ast.Cintand, _ -> failwith "internal: wrong argument to intand"
      | Ast.Cintor, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_or x y "or" builder)
      | Ast.Cintor, _ -> failwith "internal: wrong argument to intor"
      | Ast.Cintxor, [x; y] ->
        Mixedvector.singleton int_size (Llvm.build_xor x y "xor" builder)
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
        Mixedvector.null
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
        Mixedvector.singleton int_size addr
      | Ast.Cfree _, [addr] ->
        let free =
          match Llvm.lookup_function "free" the_module with
          | Some free -> free
          | None -> assert false in
        ignore (Llvm.build_call free (Array.of_list [addr]) "free" builder);
        Mixedvector.null
      | Ast.Cfree _, _ -> failwith "internal: wrong argument to free"
      | Ast.Cload a, [addr] ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_inttoptr addr
                        (Llvm.pointer_type a_struct) "memptr" builder in
        let lstruct = Llvm.build_load mem_ptr "lstruct" builder in
        unpack_encoded_value lstruct a
      | Ast.Cload _, _ -> failwith "internal: wrong argument to load"
      | Ast.Cstore a, (addr :: _)  ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_inttoptr addr
                        (Llvm.pointer_type a_struct) "memptr" builder in
        (* The following depends on the encoding of box and pairs and
         * is probably fragile! *)
        let _, venc = Mixedvector.takedrop argenc (Profile.singleton int_size) in
        let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
        ignore (Llvm.build_store v_packed mem_ptr builder);
        Mixedvector.null
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
        Mixedvector.singleton int_size addr
      | Ast.Carrayalloc _, _ -> failwith "internal: wrong argument to arrayalloc"
      | Ast.Carrayfree _, [addr] ->
        let free =
          match Llvm.lookup_function "free" the_module with
          | Some free -> free
          | None -> assert false in
        ignore (Llvm.build_call free (Array.of_list [addr]) "free" builder);
        Mixedvector.null
      | Ast.Carrayfree _, _ -> failwith "internal: wrong argument to arrayfree"
      | Ast.Carrayget a, [addr; idx] ->
        let a_struct = packing_type a in
        let offset =
          let p1 = Llvm.build_mul idx (Llvm.size_of a_struct) "p1" builder in
          Llvm.build_add addr p1 "offset" builder in
        Mixedvector.singleton int_size offset
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
      Mixedvector.add_incoming (encoded_value, src_block) phi
    (* add (encoded_value, source) to phi node *)
    with Not_found ->
      (* TODO: need no phi nodes of degree 1 *)
      begin
        position_at_start (get_block dst) builder;
        let phi = Mixedvector.build_phi
                    (encoded_value, src_block) builder in
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
                Mixedvector.takedrop ebody (Profile.singleton (log n)) in
              let cond = Mixedvector.llvalue_of_singleton ienc in
              cond, ya in
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
