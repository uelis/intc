open Core.Std
open OUnit2
  
let files_in_dir dir_name extension =
  let files = ref [] in
  let dir = Unix.opendir dir_name in
  begin
    try
      while true do
        let file = Unix.readdir dir in
        if String.is_suffix ~suffix:extension file then
          files := (dir_name ^ "/" ^ file) :: !files
      done
    with
    | End_of_file ->
      Unix.closedir dir
  end;
  !files

let parse s =
  let lexbuf = Lexing.from_string s in
  Parser.decls Lexer.main lexbuf

let read_decls filename =
  filename
  |> In_channel.read_all
  |> parse
  |> Decl.expand_all

let compile = function Decl.TermDecl(x, ast) ->
  ast
  |> Typing.check_term [] [] 
  |> Circuit.of_typedterm
  |> Ssa.of_circuit (Ident.to_string x)
  |> Trace.trace
  |> Trace.shortcut_jumps
  |> Llvmcodegen.llvm_compile

let run_llvm test_ctx llvm =
  let bc, bc_fd  = Unix.mkstemp "main.bc" in
  ignore (Llvm_bitwriter.write_bitcode_to_fd llvm bc_fd);
  Unix.close bc_fd;
  let exe, exe_fd = Unix.mkstemp "exe" in
  let out, out_fd = Unix.mkstemp "output" in
  Unix.close exe_fd;
  Unix.close out_fd;
  let res =
    let open Result in
    Unix.system
      ("llvm-link " ^ bc ^ " salloc.s " ^
       "|  opt -always-inline -O3 " ^
       "| llc -O3 " ^
       "| gcc -x assembler - -o " ^ exe) >>= fun () ->
    Unix.system ("./" ^ exe ^ " > " ^ out) >>| fun () ->
    let output = In_channel.read_all out in
    logf test_ctx `Info "Output: \n%s" output;
    output in
  Unix.remove out;
  Unix.remove exe;
  Unix.remove bc;
  res

let run_int_main test_ctx filename =
  filename
  |> read_decls
  |> List.filter ~f:(function Decl.TermDecl(f, _) -> Ident.to_string f = "main")
  |> List.map ~f:(fun d -> d |> compile |> run_llvm test_ctx)
       
let test_of_file filename =
  filename >::
  (fun test_ctx ->
     match run_int_main test_ctx filename with
     | [ Result.Ok actual ] ->
       let expected = In_channel.read_all (filename ^ ".expected") in
       assert_equal actual expected
     | _ ->
       assert_failure "compilation error or more than one main definition")
  
let test_fail_file filename =
  filename >::
  ( fun _ ->
     let fails =
       begin
         try
           ignore (filename
                   |> read_decls
                   |> List.map ~f:compile);
           false
         with
         | _ -> true
       end in
     if not fails then
       assert_failure (filename ^ " should not be accepted."))

let success_tests = files_in_dir "Tests" ".int"
let fail_tests = files_in_dir "Tests/Should_fail" ".int"
    
let suite =
  "intc tests" >:::
    ["success tests" >:::
     (success_tests |> List.map ~f:test_of_file);
     "fail tests" >:::
     (fail_tests |> List.map ~f:test_fail_file)
    ]

let () =
  run_test_tt_main suite
