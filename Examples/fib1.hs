module Main where
import Data.Int

fib :: Int64 -> Int64
fib n = if n < 2 then 1 else (fib (n-1)) + (fib (n-2))

main =
   print (fib 38)
