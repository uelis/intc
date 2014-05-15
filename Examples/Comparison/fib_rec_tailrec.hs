module Main where
import Data.Int

fib :: Int64 -> Int64
fib n = 
   let tr i acc = if i < 2 then acc else tr (i-2) (fib (i-1) + acc) in
     tr n 1

main =
   print (fib 38)
