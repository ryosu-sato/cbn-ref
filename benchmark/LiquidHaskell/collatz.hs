-- Main.hs
module Main where

{-@ div_ :: Int -> {v:Int | v != 0} -> Int @-}
div_ :: Int -> Int -> Int
div_ = div

test2 x =
  div_ x (collatz x + 1)
  where
    collatz :: Int -> Int
    collatz n
      | n == 1 = 1
      | n `mod` 2 == 0 = collatz (div_ n 2)
      | otherwise = collatz (3*n+1)

main :: IO ()
main = return ()
