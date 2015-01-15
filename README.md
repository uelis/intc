# Experimental Int Compiler

This is an experimental implementation of an Int compiler.
Int is a language that explores higher-order types for the
organisation of low-level code.

The core of the language is described in the PPDP 2014 paper
[Organising Low-Level Programs using Higher Types](http://www2.tcs.ifi.lmu.de/~schoepp/Docs/ssa.pdf).
The syntax in the implementation has changed since the submission
of this paper. The implementation referred to in this paper is
still available with tag
[ppdp14](https://github.com/uelis/intc/tree/ppdp14).

The type system currently implements the fragment of types
written mathematically as
```
  A, B  ::=  α  |  unit  |  int  |  A x B  |  A + B  |  μ α. A
  X, Y  ::=  α  |  A → X  |  X ⊗ Y  |  A·X ⊸ Y
```
These types are described in the
[PPDP paper](http://www2.tcs.ifi.lmu.de/~schoepp/Docs/ssa.pdf).

The concrete syntax for the types is:
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

### Computations

Computations are handeled using a monadic type `[A]`, where
`A` is a value type. Its terms are computations that return a
value of type `A`.

A computation term that returns value:
```rust
let t1 = 
  return 3
```
Computations can be evaluated and their result value be bound to
variables.
```rust
let t2 = 
  val v = t1 in
  val w = intadd(v, v) in
  return w
```
In this program `v` is a value variable and `t1` is evaluated only
once.

The compiler generates code for the `main` term:
```rust
let main : [unit] =
  val v = t2 in
  print v
```

### Value Functions

Functions that take values as arguments can be defined as follows.

```rust
let f : int -> [unit] =
  fn v ->
    val w = intmul(v, v) in
    print w

let main =
  f 5
```    

### Higher-Order Functions

Higher-order functions are available as well. 
```rust
let comp = \f -> \g -> \x -> f (g x)
```
They are compiled using an interactive interpretation, which can
avoid heap allocations of closures, see the PPDP paper for details.

The examples in the directory `Examples` define combinators for
tail recursion and recursion.
```rust
let tailrec : (('a -> ['b]) -> 'a -> ['b]) -> 'a -> ['b]) = ...
let fix : (''a -> ''a) -> ''a = ...
```
Note that `'a` is a value type variable and `''a` ranges
over computation and higher-order types.

Using these combinators, one can define recursive function as
follows:
```rust
/* factorial with accumulator */
let facaux : int * int -> [unit] =
  tailrec (\ facaux ->
    fn (i, acc) ->
      val b = inteq(i, 0) in
      if b then return acc else
        val i' = intsub(i, 1) in
	val acc' = intmul(acc, i) in
        facaux (i', acc')
)

/* factorial */
let fac : int -> [unit] =
  fn i ->
   facaux (i, 1)
```
   
```rust
/* fibonacci */
let fib = fix (\ fib ->
   copy fib as fib1, fib2 in
   fn i ->
     /* slt = signed less than */
     val b = intslt(i, 2) in
     if b then return 1
     else
       val f1 = val i' = intsub(i,1) in fib1 i' in
       val f2 = val i' = intsub(i,2) in fib2 i' in
       intadd(f1, f2)
   )
```

```rust
let main =
  val v = fac 10 in
  print v; print "\n";
  val w = fib 10 in
  print w
```

### Data Types

Instead of recursive value types, the implementation uses boxed types
`box<A>`. These are stored on the heap and can be allocated using the
primitive operation `alloc()`. A value `s: A` can be stored in `b` with
the operation `store(b, x)`. Values can be read using the operation
`load()`. Finally, a box is deallocated using `free(b)`.

In this experimental implementation memory safety is not enforced, e.g. the
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
