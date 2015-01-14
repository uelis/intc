open Ocamlbuild_plugin;;

flag ["link"; "ocaml"; "g++"] (S[A"-cc"; A"g++"]);;

List.iter
  (fun tag ->
     pflag ["ocaml"; tag] "pa_ounit_lib"
       (fun s -> S[A"-ppopt"; A"-pa-ounit-lib"; A"-ppopt"; A s]))
  ["ocamldep"; "compile"; "doc"]
