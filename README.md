# Experimental Int Compiler

This is an experimental implementation of an Int compiler.
The core of the language is described in the PPDP 2014 paper
[Organising Low-Level Programs using Higher Types](http://www2.tcs.ifi.lmu.de/~schoepp/Docs/ssa.pdf).
The syntax in the implementation has changed since the submission
of this paper. The implementation referred to in this paper is
available with tag
[ppdp14](https://github.com/uelis/intc/tree/ppdp14).

The type system currently implements the fragment of types
written mathematically as
```
  A, B  ::=  α  |  unit  |  int  |  A x B  |  A + B  |  μ α. A
  X, Y  ::=  α  |  A → X  |  X ⊗ Y  |  A·X ⊸ Y
```
(Universal quantification is used implicitly for external
definitions.)

The concrete syntax currently is:
```
  A, B  ::=  'a  | unit | int | A * B | A + B | box<A> | data<A1,...,An>
  X, Y  ::=  ''a  |  A -> X  | X # Y |  {A}X -> Y
```
Here, `data` is the name of an algebraic data type, that may be defined
much like in OCaml.

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

Instead of recursive value types, the implementation uses boxed types
`box<A>`. These are stored on the heap and can be allocated using the
primitive operation `alloc()`. A value `s: A` can be stored in `b` with
the operation `store(b, x)`. Values can be read using the operation
`load()`. Finally, a box is deallocated using `free(b)`.

In this experimental implementation memory safety is not enforced, i.e. the
programmer must take care to not unbox a term twice.

Example:

```rust
type list<'a> =
        Nil of unit
      | Cons of 'a * box<list<'a>>

/* list reversal */
let revaux =
   tailrec (λ rev ->
      fn (l, r) ->
        case l of
          Nil -> return r
        | Cons(x, xs) ->
           /* We have xs : box<list<'a>>.
              Using load, we obtain tail: list<'a>. */
           let tail = load(xs) in
      	   /* We can reuse the box to build up the accumulator: */
           let () = store(xs, r) in
           rev(tail, Cons(x, xs))
      )

fn rev(l) =
  revaux (l, Nil)

/* map */
let maprev = λ f ->
   tailrec (λ mapf ->
      fn (l, r) ->
        case l of
          Nil -> return r
        | Cons(x, xs) ->
            let tail = load(xs) in
            let () = store(xs, r) in
            let y = f x in
            mapf(tail, Cons(y, xs))
      )

let maptr = λ f ->
   fn l ->
      let l1 = maprev f (l, Nil) in
      rev l1

let printlist = tailrec (λ printlist ->
    fn l ->
       case l of
           Nil ->
            print "\n"
         | Cons(h, t) ->
            print h;
            print " ";
            let tail = load(t) in
            let () = free(t) in
            printlist tail
    )

fn upto(n) =
   tailrec (λ aux ->
   fn (m, r) ->
      let b = inteq(m, 0) in
      if b then return r else
        let m' = intsub(m, 1) in
        let tail = alloc() in
        let () = store(tail, r) in
        aux (m', Cons(m, tail))
   ) (n, Nil)

let main =
   let l = upto 20 in
   let l' = maptr (fn i -> intmul(2, i)) l in
   let l'' = rev l' in
   printlist l''
```
