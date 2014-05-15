# Experimental Int Compiler

## Installation

The compiler is writen in OCaml and depends on Jane Street's Core
library and the OCaml LLVM bindings. 

The dependencies are most easily installed using the 
OCaml Package Manager (OPAM).

```  
  opam install core
  opam install llvm
  make
```

OPAM itself can be obtained from (http://opam.ocamlpro.com).
On Ubuntu 14.04, it can be installed with `apt-get install opam`.
  
## Compiling Examples

```
  $ ./intc.native Examples/euler.int
```
This generates an LLVM bitcode file `main.bc`, which can be
compiled to an executable `main` using the script `llvm_compile.sh`:
```
  $ ./llvm_compile.sh main
```

 
