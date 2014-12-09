open Core.Std

let var_name basename i =
   basename ^ (string_of_int i)

let index_of_varname basename name =
   match String.chop_prefix ~prefix:basename name with
    | None -> -1
    | Some suffix ->
      try int_of_string suffix with Failure "int_of_string" -> -1

let mkVarGenerator (basename: string) ~avoid:(avoid: string list)
  : unit -> string =
  let max_index =
    List.fold avoid
      ~init:(-1)
      ~f:(fun acc v -> max acc (index_of_varname basename v)) in
  let next_var_index = ref max_index in
  let gen () =
    incr next_var_index;
    var_name basename !next_var_index
  in gen
