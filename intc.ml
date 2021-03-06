open Core.Std
open Lexing
  
let file_name = ref "" 

let location_msg startline startcolumn endline endcolumn =
  if endline = startline then
    Printf.sprintf "File \"%s\", line %i, column %i-%i:"
      !file_name startline startcolumn endcolumn
  else
    Printf.sprintf "File \"%s\", line %i, column %i- line %i, column %i:"
      !file_name startline startcolumn endline endcolumn

let parse_error_loc lexbuf =
  let s = lexbuf.lex_start_p in
  let sline = s.pos_lnum in
  let scolumn = s.pos_cnum - s.pos_bol + 1 in
  let e = lexbuf.lex_curr_p in
  let eline = e.pos_lnum in
  let ecolumn = e.pos_cnum - e.pos_bol + 1 in
  location_msg sline scolumn eline ecolumn

(* For error reporting: compute a string of where the error occurred *)
let term_loc (s : Ast.t option) =
  match s with
  | None -> ""
  | Some s ->
    let open Ast in
    let open Ast.Location in
    match s.loc with
    | Some(loc) ->
      location_msg loc.start_pos.line loc.start_pos.column
        loc.end_pos.line loc.end_pos.column
    | None -> "Term " ^ (Printing.string_of_ast s)


let error_msg loc msg = if loc = "" then msg else loc ^ " " ^ msg
let exit_with_error loc msg =
  Printf.fprintf stderr "%s\n%!" (error_msg loc msg);
  exit 1

let parse (s: string) : Decl.t list =
  let lexbuf = Lexing.from_string s in
  try
    Parser.decls Lexer.main lexbuf
  with
  | Parsing.Parse_error ->
    exit_with_error (parse_error_loc lexbuf) "Parse error"
  | Decl.Illformed_decl(msg) ->
    exit_with_error (parse_error_loc lexbuf) ("Syntax error. " ^ msg)

let compile (d: Decl.t) : unit =
  match d with
  | Decl.TermDecl(f, ast) ->
    let f_name = Ident.to_string f in
    let circuit =
      try
        let t = Typing.check_term [] [] ast in
        let circuit = Circuit.of_typedterm t in
        Printf.printf "%s : %s\n"
          (Ident.to_string f)
          (Printing.string_of_type ~concise:(not !Opts.print_type_details)
             t.Typedterm.t_type);
        circuit
      with Typing.Typing_error(s, err) ->
        let msg = err ^ "\nIn declaration of '" ^ f_name ^ "'." in
        raise (Failure (error_msg (term_loc s) msg)) in
    flush stdout;
    if !Opts.keep_circuits then
      begin
        let target = Printf.sprintf "%s.dot" f_name in
        Out_channel.write_all target ~data:(Circuit.dot_of_circuit circuit)
      end;
    if !Opts.keep_ssa then
      begin
        let ssa_func = Ssa.of_circuit f_name circuit in
        let ssa_traced = Trace.trace ssa_func in
        let ssa_shortcut = Trace.shortcut_jumps ssa_traced in
        let write_ssa filename ssafunc =
          Out_channel.with_file filename
            ~f:(fun c -> Ssa.fprint_func c ssafunc) in
        let target = Printf.sprintf "%s.ssa" f_name in
        Printf.printf
          "*** Writing ssa-form program for %s to file '%s'\n" f_name target;
        write_ssa target ssa_func;
        let target = Printf.sprintf "%s.ssa.traced" f_name in
        Printf.printf
          "*** Writing ssa-form program for %s to file '%s'\n" f_name target;
        write_ssa target ssa_traced;
        let target = Printf.sprintf "%s.ssa.shortcut" f_name in
        Printf.printf
          "*** Writing ssa-form program for %s to file '%s'\n" f_name target;
        write_ssa target ssa_shortcut
      end;
    if !Opts.llvm_compile && (f_name = "main") then
      begin
        let ssa_func = Ssa.of_circuit f_name circuit in
        let ssa_traced = Trace.trace ssa_func in
        let ssa_shortcut = Trace.shortcut_jumps ssa_traced in
        let target = Printf.sprintf "%s.bc" f_name in
        let llvm_module = Llvmcodegen.llvm_compile ssa_shortcut in
        ignore (Llvm_bitwriter.write_bitcode_file llvm_module target)
       end

let arg_spec =
  [("--type-details", Arg.Set Opts.print_type_details,
    "Print full type details, including subexponentials.");
   ("--verbose", Arg.Set Opts.verbose,
    "Print compilation details..");
   ("--circuits", Arg.Set Opts.keep_circuits,
    "Keep circuit for each declaration (f.dot).");
   ("--ssa", Arg.Set Opts.keep_ssa,
    "Keep ssa program for each declaration (f.ssa).");
   ("--llvm", Arg.Set Opts.llvm_compile,
    "Keep llvm bitcode for each declaration (f.bc).");
  ]

let usage_msg = "Usage: intc input.int\nOptions:"

let () =
  try
    Arg.parse arg_spec (fun s -> file_name := s) usage_msg;
    if !file_name = "" then
      Printf.printf "No input file.\n"
    else
      begin
        if !Opts.keep_ssa then
          Printf.printf "*** Writing ssa files.\n%!";
        if !Opts.llvm_compile then
          Printf.printf "*** Writing llvm bitcode files.\n%!";
        let input = In_channel.read_all !file_name in
        let decls = parse input in
        let substituted_decls = Decl.expand_all decls in
        List.iter ~f:compile substituted_decls
      end
  with
  | Sys_error msg 
  | Failure msg ->
    exit_with_error "" msg
  | Typing.Typing_error(t, msg)->
    exit_with_error (term_loc t) msg
