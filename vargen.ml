
let mkVarGenerator (basename: string) ~avoid:(avoid: string list) : unit -> string =
  let next_var_index = ref 0 in
  let rec gen () =
    let i = !next_var_index in
      next_var_index := i + 1; 
      let v = basename ^ (string_of_int i) in
        if List.mem v avoid then gen () else v
  in gen
