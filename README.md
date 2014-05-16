# Experimental Int Compiler

This is an experimental implementation of an Int compiler.

The type system currently implements the fragment of types
written mathematically as 
```
  X, Y  ::=  α  |  A → TB  |  A·X ⊸ Y
```
(Universal quantification is used implicitly for external
definitions.)

The concrete syntax currently is:
```
  X, Y  ::=  'a  |  A -> B  |  {A}|X| -> Y
```

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

## Examples

### Data Types in the Low-Level Language

Instead of recursive value types, the implementated uses boxed types
`box<A>` with a term `box(s) : box<A>` if `s: A` and a term 
`unbox(t) : A` if `t : box<A>`. Evaluating `box(s)` makes a heap
allocation and returns the address. The term `unbox(t)` reads from
the heap and frees the memory. In this experimental implementation
memory safety is not enforced, i.e. the programmer must take care
to not unbox a term twice.

Example:

```rust
  type list<'a> = 
          Nil of unit 
        | Cons of 'a * box<list<'a>>

let maprev = fun f ->
   tailrec (fun mapf ->
      fn (l, r) {
        case l of
          Nil -> r
        | Cons(x, xs) -> mapf(unbox xs, Cons(f x, box r))
      })

let revaux =
   tailrec (fun rev ->
      fn (l, r) {
        case l of
          Nil -> r
        | Cons(x, xs) -> rev(unbox xs, Cons(x, box r))
      })

fn rev(l) {
  revaux (l, Nil())
}

let maptr = fun f -> 
   fn l {
      rev (maprev f (l, Nil))
   }

let printlist = tailrec (fun printlist ->
    fn l { 
       case l of 
           Nil -> 
            print "\n"
         | Cons(h, t) ->
            print h;
            print " ";
            printlist (unbox t)
    })

```
