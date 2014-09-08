open Lexing
open Opts
open Decls

(* Xavier Leroy posted this on the OCaml mailing list *)
let read_file filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let s = String.create len in
  really_input ic s 0 len;
  close_in ic;
  s

let write_file filename s = 
  let oc = open_out filename in 
  Printf.fprintf oc "%s" s;
  close_out oc

let parse_error_loc lexbuf =
  let start_pos = lexbuf.lex_start_p in
  Printf.sprintf "line %i, character %i:"
    (start_pos.pos_lnum) (start_pos.pos_cnum - start_pos.pos_bol + 1)

let error_msg loc msg = loc ^ " " ^ msg
let print_error loc msg = print_string (error_msg loc msg)
let line_column_loc (line : int) (column : int ) = 
  Printf.sprintf "line %i, column %i:" line column  

let parse (s: string) : decls =
  let lexbuf = Lexing.from_string s in
  try 
    Parser.decls Lexer.main lexbuf
  with 
  | Parsing.Parse_error -> 
    failwith (error_msg (parse_error_loc lexbuf) "Parse error")
  | Decls.Non_Wellformed(msg, l, c) -> 
    failwith (error_msg (line_column_loc l c) ("Syntax error. " ^ msg))

(* For error reporting: compute a string of where the error occurred *)
let term_loc (s : Term.t option) = 
  match s with
    | None -> ""
    | Some s ->
        match s.loc with
          | Some(loc) when loc.start_pos.line = loc.end_pos.line -> 
              Printf.sprintf "line %i, columns %i-%i:" 
                loc.start_pos.line loc.start_pos.column loc.end_pos.column
          | Some(loc) -> 
              Printf.sprintf "line %i, column %i to line %i, column %i:" 
                loc.start_pos.line loc.start_pos.column
                loc.end_pos.line loc.end_pos.column
          | None -> "Term " ^ (Printing.string_of_term s) 

let rec compile_passes (d: decls) : unit = 
  match d with
  | [] -> ()
  | TermDecl(f, t) :: r ->
    let t = Term.freshen_type_vars t in
    let b = 
      try
        Typing.principal_type [] [] t 
      with Typing.Typing_error(s, err) ->
        let msg = "Typing error when checking upper " ^
                  "class declaration of '" ^ f ^ "'.\n" ^ err ^ "\n" in
        raise (Failure (error_msg (term_loc s) msg)) in 
    let t = Canonise.canonise t in
    let circuit = Circuit.circuit_of_termU t in
    Printf.printf "%s : %s\n" f  
      (Printing.string_of_type ~concise:(not !opt_print_type_details) b);
    (* Printing.print_term t;  *)
    if !opt_keep_circuits then
      begin
        let target = Printf.sprintf "%s.dot" f in
        write_file target
          (Circuit.dot_of_circuit circuit)
      end;
    begin
      let ssa_func = Ssa.circuit_to_ssa f circuit in
      let ssa_traced = Trace.trace ssa_func in
      let ssa_shortcut = Trace.shortcut_jumps ssa_traced in
      if !opt_keep_ssa then
        begin
          let target = Printf.sprintf "%s.ssa" f in
          Printf.printf "*** Writing ssa-form program for %s to file '%s'\n" f target;
          write_file target (Ssa.string_of_func ssa_func);
          let target = Printf.sprintf "%s.ssa.traced" f in
          Printf.printf "*** Writing ssa-form program for %s to file '%s'\n" f target;
          write_file target (Ssa.string_of_func ssa_traced);
          let target = Printf.sprintf "%s.ssa.shortcut" f in
          Printf.printf "*** Writing ssa-form program for %s to file '%s'\n" f target;
          write_file target (Ssa.string_of_func ssa_shortcut)
        end;
      if !opt_llvm_compile then
        begin
          let target = Printf.sprintf "%s.bc" f in
          let llvm_module = Llvmcodegen.llvm_compile ssa_shortcut in
          ignore (Llvm_bitwriter.write_bitcode_file llvm_module target)
        end
    end;
    compile_passes r

let arg_spec =     
  [("--type-details", 
    Arg.Unit (fun _ -> opt_print_type_details := true), 
    "Print full type details, including subexponentials.");
   ("--circuits", 
    Arg.Unit (fun _ -> opt_keep_circuits := true), 
    "Keep circuit for each declaration (f.dot).");
   ("--ssa", 
    Arg.Unit (fun _ -> opt_keep_ssa := true), 
    "Keep ssa program for each declaration (f.ssa).");
   ("--llvm", 
    Arg.Unit (fun _ -> opt_llvm_compile := true), 
    "Keep llvm bitcode for each declaration (f.bc).");
  ]

let usage_msg = "Usage: intc input.int\nOptions:"  

let main = 
  try 
    let file_name = ref "" in
    Arg.parse arg_spec (fun s -> file_name := s) usage_msg;
    if !file_name = "" then 
      Printf.printf "No input file.\n"
    else 
      begin
        if !opt_keep_ssa then 
          Printf.printf "*** Writing ssa files.\n";
        if !opt_llvm_compile then 
          Printf.printf "*** Writing llvm bitcode files.\n";
        let input = read_file !file_name in
        let decls = parse input in
        let substituted_decls = subst_decls decls in
        compile_passes substituted_decls
      end
  with 
  | Failure msg -> Printf.printf "%s\n" msg
  | Typing.Typing_error(t, msg)-> print_error (term_loc t) msg

