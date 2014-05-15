module Main where
import Data.Int

val = \n -> \k -> k n
add = \k -> k (\n -> \k1 -> 
                          k1 (\m -> \k2 -> 
                              let s = (n + m) in
                                k2 s))
app = \e1 -> \e2 -> \k -> e1 (\x1 -> e2 (\x2 -> x1 x2 k))
mem = \f -> \k -> let n = f (\r -> r) in k n

step1 =
   \f ->
     val (\x-> mem (\k ->
          if x < 2 then val (1 ::Int64) k else
              app (app add (f (x - 1))) (f (x - 2)) k 
         ))

fixv = step1 (\x -> \k -> fixv (\b -> b x k))

fib :: Int64 -> Int64
fib n = app (fixv) (val n) (\r -> r) 
main =
  print (fib 38)
