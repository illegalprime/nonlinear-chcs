module Main where

import Z3.Monad

script :: Z3 (Maybe [Integer])
script = do
  x <- mkFreshIntVar "x"
  y <- mkFreshIntVar "y"
  x' <- mkFreshIntVar "xp"
  y' <- mkFreshIntVar "yp"



main :: IO ()
main = putStrLn "Hello, Haskell!"
